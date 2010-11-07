open Type
open Util

(* TODO This module is a little messy. *)

exception Undefined
exception Break

(* Select axioms that refer only to unary operations and constants. *)
let part_axioms axioms =
  let rec no_binary = function
    | Binary _ -> false
    | Unary (_, t) -> no_binary t
    | Var _ | Const _ -> true in
  let no_binary_axiom (eq1, eq2) = no_binary eq1 && no_binary eq2 in
  List.partition no_binary_axiom axioms


(*
   Partition unary axioms. In the first part are the axioms of the form
   f(a) = b, where a and b are constants, and the rest in the second one.
*)
let part_unary_axioms axioms =
  let is_simple = function
    | (Unary (_,Const _), Const _)
    | (Const _, Unary (_,Const _)) -> true
    | _ -> false
  in List.partition is_simple axioms

(*
   Partition binary axioms into two parts. In the first are axioms of the form
   a + b = c, where a b and c are constants or unary applications, these are termed simple,
   and the rest are in the second part, these I call complicated.
*)
let part_binary_axioms axioms =
  let rec const_and_unary = function
    | (Unary (_,t)) -> const_and_unary t
    | (Const _ ) -> true
    | _ -> false in
  let is_simple = function
    | (Binary (_,t1,t2), Const _)
    | (Const _, Binary (_,t1,t2)) -> const_and_unary t1 && const_and_unary t2
    | _ -> false
  in List.partition is_simple axioms

(*
  Partition binary axioms into two parts.
  The first:
     axioms f(a) * g(a) = h(a) or some of the expressions contain a constant
  The second:
     all the rest. :)
  We can immediately apply the first kind.
*)

let part_one_var_binary axioms =
  let rec const_var_unary = function
    | (Unary (_,t)) -> const_var_unary t
    | (Const c ) -> Some (Const c)
    | (Var v) -> Some (Var v)
    | _ -> None in
  let is_simple = function
    | (Binary (_,t1,t2), t3)
    | (t3, Binary (_,t1,t2)) ->
      let v1 = const_var_unary t1 in
      let v2 = const_var_unary t2 in
      let v3 = const_var_unary t3 in
      begin
        match (v1,v2,v3) with
          (* This could be more easily done with a list *)
          | (Some (Const _), Some (Const _), Some (Const _))
          | (Some (Var _), Some (Const _), Some (Const _))
          | (Some (Const _), Some (Var _), Some (Const _))
          | (Some (Const _), Some (Const _), Some (Var _)) -> true
          | (Some (Var v1), Some (Var v2), Some (Const _))
          | (Some (Var v1), Some (Const _), Some (Var v2))
          | (Some (Const _), Some (Var v1), Some (Var v2)) -> v1 = v2
          | (Some (Var v1), Some (Var v2), Some (Var v3)) -> v1 = v2 && v2 = v3
          | (None,_,_) | (_,None,_) | (_,_,None) -> false
          | _ -> invalid_arg "Binary operation creeped in part_one_binary.is_simple."
      end
    | _ -> false
  in List.partition is_simple axioms

(* Select associativity axioms. *)

let partition_assoc axioms =
  let is_assoc = function
    | (Binary (op1, Binary (op2, Var a1, Var b1), Var c1), Binary (op3, Var a2, Binary (op4, Var b2, Var c2)))
    | (Binary (op3, Var a2, Binary (op4, Var b2, Var c2)), Binary (op1, Binary (op2, Var a1, Var b1), Var c1))
        when op1 = op2 && op2 = op3 && op3 = op4 && a1 = a2 && b1 = b2 && c1 = c2 -> true
    | _ -> false
  in List.partition is_assoc axioms


let make_3d_array x y z initial =
  Array.init x (fun _ -> Array.make_matrix y z initial)

(*
  Depth of an axiom is maximum of the depths of the equations.
  Depth of an equation is the number of binary operations in it.
*)
let axiom_depth (left, right) =
  let rec term_depth acc = function
    | (Unary (_,t)) -> term_depth acc t
    | (Var _) | (Const _) -> acc
    | (Binary (_,t1,t2)) -> term_depth (term_depth (1+acc) t1) t2
  in max (term_depth 0 left) (term_depth 0 right)

(*
  List of distinct variables of a term.
*)
let rec
    eq_vars acc = function
      | Const _ -> acc
      | Var v -> if List.mem v acc then acc else (v :: acc)
      | Binary (_,t1,t2) -> let lv = eq_vars acc t1 in
                            eq_vars lv t2
      | Unary (_,t) -> eq_vars acc t

(*
  List of distinct variables of an axiom.
*)
let dist_vars (left, right) =
  let lv = eq_vars [] left in eq_vars lv right

(*
  Number of distinct variables in an axiom.
  Could also look for maximum variable index.
*)
let num_dist_vars a = List.length (dist_vars a)

(* Amenable axioms are the ones where left and right terms have binary op
   as outermost operation and have exactly the same variables on left and right sides. *)
let partition_amenable axioms =
  let is_amenable ((left, right) as axiom) =
      match axiom with
        | (Binary _, Binary _)->
          List.sort compare (eq_vars [] left) = List.sort compare (eq_vars [] right)
        | ((Binary _), _) -> Util.is_sublist (eq_vars [] right) (eq_vars [] left)
        | (_, (Binary _)) -> Util.is_sublist (eq_vars [] left) (eq_vars [] right)
        | _ -> false in
  List.partition is_amenable axioms


(* ************************************************************************** *)
(* Main search functions. *)

(*
  Generate binary operation tables. lc, lu and lb are numbers of constants,
  unary and binary operations. unary_arr is supposed to be a matrix
  of unary operations where each line is an operation. axioms
  should only contain axioms where there is at least one binary
  operation.
*)
let gen_binary n lc lu lb axioms unary_arr k =
  let (simple, complicated) = part_binary_axioms axioms in

  (*
     Main operation tables.
  *)
  let binary_arr = make_3d_array lb n n (-1) in

  (*
     Applies simple axioms to the main operation tables.
     If axioms aren't simple it fails miserably.
  *)
  let apply_simple axiom =
    let rec get_value = function
      | (Const c) -> c
      | (Unary (op,v)) -> unary_arr.(op).(get_value v)
      | _ -> invalid_arg "Ooops, binary operation or variable in apply_simple.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), Const c)
      | (Const c, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        binary_arr.(op).(v1).(v2) <- c
      | _ -> invalid_arg "Not a simple binary axiom."
  in List.iter apply_simple simple ;

  (*
     left are the axioms which cannot be immediately applied
     These include axioms of depth > 1 and those with more variables.
  *)

  let (one_var_shallow, left) = part_one_var_binary complicated in

  (*
    Apply one variable shallow axioms. Typical example is axioms for
    a unit element in a monoid (forall a: a * e = e)
  *)

  let apply_one_var axiom elem =
    let rec get_value = function
      | (Const c) -> c
      | (Var _) -> elem
      | (Unary (op,v)) -> unary_arr.(op).(get_value v)
      | _ -> invalid_arg "Ooops, binary operation in apply_one_var.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), t3)
      | (t3, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        let v3 = get_value t3 in
        binary_arr.(op).(v1).(v2) <- v3
      | _ -> invalid_arg "not a legal axiom in apply_one_var"
  in
  for i=0 to n-1 do
    List.iter (fun x -> apply_one_var x i) one_var_shallow
  done ;

  (*
     Partition axioms. Assoc and amenable are naturally associativity and amenable axioms.
     zippep_axioms are the rest that have to be checked differently than amenable.
     Zipped means in the form (number of distinct variables, axioms)
  *)
  let (assoc, amenable, zipped_axioms) =
    let (assoc, rest) = partition_assoc left in
    let (amenable, rest) = partition_amenable rest in
    (assoc,
     List.map (fun a -> num_dist_vars a, a) amenable,
     (* Check axioms with fewer free variables first. *)
     List.sort (fun (n,_) (m,_) -> compare n m) (List.map (fun a -> (num_dist_vars a, a)) rest)) in

  let max_vars = List.fold_left max 0 (List.map num_dist_vars left) in

  (* This could potentially gobble up memory. TODO *)
  let all_tuples = Array.init (max_vars + 1) (fun i -> ntuples n i) in

  (*
     evaluate term in the context of vars. Raises Undefined if there is
     insufficient information to fully evaluate.
  *)
  let rec eval_eq vars = function
    | Const c -> c
    | Var v -> vars.(v)
    | Unary (op, t) ->
      begin match eval_eq vars t with
        | -1 -> raise Undefined
        | v -> unary_arr.(op).(v)
      end
    | Binary (op, lt, rt) ->
      begin match eval_eq vars lt with
        | -1 -> raise Undefined
        | lv ->
          begin match eval_eq vars rt with
            | -1 -> raise Undefined
            | rv -> binary_arr.(op).(lv).(rv)
          end
      end
  in


  (*
     Returns false if there is a conflict.
  *)
  let axiom_ok (num_vars, (left, right)) =
    let tuples = all_tuples.(num_vars) in
    let apply_to i =
      try
        let a = eval_eq i left in (* b is not evaluated if a is -1 *)
        a = -1 ||
            let b = eval_eq i right in
            (b = -1 || a = b)
      with Undefined -> true
    in
      Util.array_for_all apply_to tuples
  in


  (* ********************************************************************* *)
  (* Auxiliary functions for computing actions from axioms and
     checking axiom validity after adding one element
  *)

  (* Compute actions from amenable axioms *)
  let actions_from_axiom (nvars, axiom) =
    let stack = Stack.create () in
    let vars = Array.make nvars (-1) in
    let nfill = ref 0 in
    let undo id =
      while not (Stack.is_empty stack) && let (id', _, _,_) = Stack.top stack in id' = id do
        let (_, op, left, right) = Stack.pop stack in
        binary_arr.(op).(left).(right) <- -1
      done in


    (* free fills the rest of the variables with all possible values *)
    let rec
        free cont term =
      if !nfill = nvars then cont ()
      else begin
        match term with
          | Var v when vars.(v) = -1 ->
            for k=0 to n-1 do
              vars.(v) <- k ;
              incr nfill ;
              cont () ;
              decr nfill ;
              vars.(v) <- -1 ;
            done
          | (Binary (_, l, r)) ->
            free (fun () -> free cont r) l
          | _ -> cont ()
      end in

    let rec
        (* generate all possible subexpressions so that the term evaluates to k *)
        gen_all k cont term =
          if !nfill = nvars then cont ()
          else begin
            match term with
              | (Binary (op, l, r)) ->
                for u=0 to n-1 do
                  for v=0 to n-1 do
                    if binary_arr.(op).(u).(v) = k then
                      gen_all u (fun () -> gen_all v cont r) l
                  done
                done
              | (Unary (op, t)) ->
                for u=0 to n-1 do
                  if unary_arr.(op).(u) = k then
                    gen_all u cont t
                done
              | Var v when vars.(v) = -1 ->
                vars.(v) <- k ;
                incr nfill ;
                cont () ;
                decr nfill ;
                vars.(v) <- -1
              | Var v when vars.(v) = k -> cont ()
              | Const c when c = k -> cont ()
              | _ -> ()
          end in

    (* We just set (i,j) to some value in o.
       See where we might use this to violate an axiom or set a new value. *)
    let rec
        fill (o,i,j) cont = function
          | (Binary (op, l, r)) when op = o ->
          (* both are in the left subtree *)
            fill (o,i,j) (fun () -> free cont r) l ;
          (* case l = i, r = j *)
            gen_all i (fun () -> gen_all j cont r) l ;
          (* both are in the right subtree *)
            fill (o,i,j)  (fun () -> free cont l) r
          | (Binary (_, l, r)) ->
          (* both are in the left subtree *)
            fill (o,i,j) (fun () -> free cont r) l ;
          (* both are in the right subtree *)
            fill (o,i,j) (fun () -> free cont l) r
          | Unary (_, t) -> fill (o,i,j) cont t
          | _ -> () in

    (*
       check_other: Check if an axiom is violated or we can set a new value.
       This is the end of continuations. It is called when all
       of the variables have been set.
    *)
    match axiom with
      | (Binary (op1, l1, r1), Binary (op2, l2, r2)) ->
        let f cont id o i j =
          for k = 0 to nvars - 1 do
            vars.(k) <- -1
          done ;
          nfill := 0 ;
          let check_other () =
            try
              let el1 = eval_eq vars l1 in
              let er1 = eval_eq vars r1 in
              let el2 = eval_eq vars l2 in
              let er2 = eval_eq vars r2 in
              if el1 <> -1 && el2 <> -1 && er1 <> -1 && er2 <> -1 then
                begin
                  let left = binary_arr.(op1).(el1).(er1) in
                  let right = binary_arr.(op2).(el2).(er2) in
                  if left <> -1 && right = -1 then
                    begin
                      binary_arr.(op2).(el2).(er2) <- left ;

                      Stack.push (id, op2, el2, er2) stack ;

                      (* Try to fill some more or fail trying *)
                      if not (cont id op2 el2 er2) then
                        raise Break
                    end
                  else if left = -1 && right <> -1 then
                    begin
                      binary_arr.(op1).(el1).(er1) <- right ;

                      Stack.push (id, op1, el1, er1) stack ;

                      (* Try to fill some more or fail trying *)
                      if not (cont id op1 el1 er1) then
                        raise Break
                    end
                  else if (* left <> -1 && right <> -1 &&  *)left <> right then
                    raise Break
                end
            with Undefined -> () in
          try
            fill (o,i,j) check_other (Binary (op2, l2, r2)) ;
            fill (o,i,j) check_other (Binary (op1, l1, r1)) ; true
          with Break -> false in (f, undo)
      | (term, Binary (op2, l2, r2))
      | (Binary (op2, l2, r2), term) ->
        let f cont id o i j =
          for k = 0 to nvars - 1 do
            vars.(k) <- -1
          done ;
          nfill := 0 ;
          let check_other () =
            try
              let el2 = eval_eq vars l2 in
              let er2 = eval_eq vars r2 in
              let elt = eval_eq vars term in
              if elt <> -1 && el2 <> -1 && er2 <> -1 then
                begin
                  let left = elt in
                  let right = binary_arr.(op2).(el2).(er2) in
                  if right = -1 then
                    begin
                      binary_arr.(op2).(el2).(er2) <- left ;

                      Stack.push (id, op2, el2, er2) stack ;

                      (* Try to fill some more or fail trying *)
                      if not (cont id op2 el2 er2) then
                        raise Break
                    end
                  else if left <> right then
                    raise Break
                end
            with Undefined -> () in
          try
            fill (o,i,j) check_other (Binary (op2, l2, r2)) ; true
          with Break -> false in (f, undo)
      | _ -> invalid_arg "Invalid axiom in actions_from_axiom. At least one term has to be binary." in

  (* Special case of actions_from_axiom for associativity axioms.
     It is ugly, but much faster.
  *)
  let actions_from_assoc = function
    | (Binary (op1, Binary (op2, Var a1, Var b1), Var c1), Binary (op3, Var a2, Binary (op4, Var b2, Var c2)))
    | (Binary (op3, Var a2, Binary (op4, Var b2, Var c2)), Binary (op1, Binary (op2, Var a1, Var b1), Var c1))
        when op1 = op2 && op2 = op3 && op3 = op4 && a1 = a2 && b1 = b2 && c1 = c2 ->
      let stack = Stack.create () in
      let f cont id o i j =
        if o <> op1 then true
        else begin
          try
            (* cases a = i, b = j, c arbitrary and b = i, c = j, a arbitrary *)
            for k = 0 to n-1 do
              (* case a=i, b=j *)
              let ab = binary_arr.(o).(i).(j) in
              let bc = binary_arr.(o).(j).(k) in
              if bc <> -1 then
                begin
                  let ab_c = binary_arr.(o).(ab).(k) in
                  let a_bc = binary_arr.(o).(i).(bc) in
                  if ab_c <> -1 && a_bc = -1 then
                    begin
                      binary_arr.(o).(i).(bc) <- ab_c ;

                      Stack.push (id,o,i,bc) stack ;

                      if not (cont id o i bc) then
                        raise Break
                    end
                  else if ab_c = -1 && a_bc <> -1 then
                    begin
                      binary_arr.(o).(ab).(k) <- a_bc ;

                      Stack.push (id, o,ab,k) stack ;

                      if not (cont id o ab k) then
                        raise Break
                    end
                  else if ab_c <> -1 && a_bc <> -1 && ab_c <> a_bc then
                    raise Break
                end ;
              (* case b = i, c = j *)
              let ab = binary_arr.(o).(k).(i) in
              let bc = binary_arr.(o).(i).(j) in
              if ab <> -1 then
                begin
                  let ab_c = binary_arr.(o).(ab).(j) in
                  let a_bc = binary_arr.(o).(k).(bc) in
                  if ab_c <> -1 && a_bc = -1 then
                    begin
                      binary_arr.(o).(k).(bc) <- ab_c ;

                      Stack.push (id,o,k,bc) stack ;

                      if not (cont id o k bc) then
                        raise Break
                    end
                  else if ab_c = -1 && a_bc <> -1 then
                    begin
                      binary_arr.(o).(ab).(j) <- a_bc ;

                      Stack.push (id, o,ab,j) stack ;

                      if not (cont id o ab j) then
                        raise Break
                    end
                  else if ab_c <> -1 && a_bc <> -1 && ab_c <> a_bc then
                    raise Break
                end ;
            done ;
            (* Cases ab = i, c = j and a = i, bc = j *)
            for a=0 to n-1 do
              for b=0 to n-1 do
                (* case ab = i *)
                if binary_arr.(o).(a).(b) = i then
                  begin
                    let bc = binary_arr.(o).(b).(j) in
                    if bc <> -1 then
                      begin
                        let a_bc = binary_arr.(o).(a).(bc) in
                        if a_bc = -1 then
                          begin
                            binary_arr.(o).(a).(bc) <- binary_arr.(o).(i).(j) ;

                            Stack.push (id,o,a,bc) stack ;

                            if not (cont id o a bc) then
                              raise Break
                          end
                        else if a_bc <> binary_arr.(o).(i).(j) then
                          raise Break
                      end
                  end ;
                (* case bc = j *)
                let (b,c) = (a,b) in
                if binary_arr.(o).(b).(c) = j then
                  begin
                    let ab = binary_arr.(o).(i).(b) in
                    if ab <> -1 then
                      begin
                        let ab_c = binary_arr.(o).(ab).(c) in
                        if ab_c = -1 then
                          begin
                            binary_arr.(o).(ab).(c) <- binary_arr.(o).(i).(j) ;

                            Stack.push (id, o, ab, c) stack ;

                            if not (cont id o ab c) then
                              raise Break
                          end
                        else if ab_c <> binary_arr.(o).(i).(j) then
                          raise Break
                      end
                  end
              done
            done ; true
          with Break -> false
        end in
      let undo id =
        while not (Stack.is_empty stack) && let (id', _, _,_) = Stack.top stack in id' = id do
          let (_, op, left, right) = Stack.pop stack in
          binary_arr.(op).(left).(right) <- -1
        done in (f, undo)
    | _ -> invalid_arg "actions_from_assoc axiom given is not associativity" in

  (*
    Checks if all axioms are still valid. This is for axioms that are not amenable.
    Amenable are checked immediately after adding each element.
  *)
  let check () = List.for_all axiom_ok zipped_axioms in

  let (dos, undos) = List.split (List.map actions_from_assoc assoc @
                                 List.map (actions_from_axiom) amenable) in

  (*
     Use all the functions from dos. Continuation passed is dodos itself.
     The idea is that once we set a new element in f we immediately call
     dodos again to check validity of other axioms and maybe add some more
     elements. This sequence of calls to dodos will eventually end. If not
     sooner than at least when all operation tables are full.
  *)
  let rec
      dodos id o i j = List.for_all (fun f -> f dodos id o i j) dos in

  let doundos id = List.iter (fun f -> f id) undos in

  (* Main loop. *)
  (* o is index of operation, (i,j) current element *)
  let rec gen_operation o = function
    | _ when o = lb ->
      k { size = n;
          const = Util.enumFromTo 0 (lc-1);
          unary =
          begin
            let r = ref [] in
            for i=0 to lu - 1 do
              r := (i, unary_arr.(i)) :: !r
            done ; !r
          end ;
          binary = let r = ref [] in
                   for i=0 to lb-1 do
                     r := (i, binary_arr.(i)) :: !r
                  done ; !r
        }
    | (i,_) when i = n -> gen_operation (o+1) (0,0)
    | (i,j) when j = n -> gen_operation o (i+1,0)
    | (i,j) when binary_arr.(o).(i).(j) = -1 ->
      for k=0 to n-1 do
        binary_arr.(o).(i).(j) <- k ;
        (* check_after_add isn't needed here because fs report back instead *)
        if dodos (o,i,j) o i j && check () then
          gen_operation o (i,j+1)
        ; doundos (o,i,j)
        ; binary_arr.(o).(i).(j) <- -1
      done
    | (i,j) ->  gen_operation o (i,j+1) in
  gen_operation 0 (0,0)


(*
  Generate unary operation tables. lc, lu and lb are numbers of constants,
  unary and binary operations.
*)
let gen_unary n lc lu lb axioms k =
  let (unary_axioms, binary_axioms) = part_axioms axioms in
  (*
     Simple and complicated unary axioms. Simple are the
     ones of the form f(c) = d or f(d) = c for c and d constants. These
     can be easily applied.
     TODO: Axioms of the form f(x) = c for x variable and c constant
     are also easily dispatched with.

     Complicated are the complement of simple and cannot be so easily applied.
  *)
  let (simple, complicated) = part_unary_axioms unary_axioms in
  (*
    Equation must not contain any binary operations.
    path_from_equation returns a 4-tuple (indicator, index, index of last operation,
    list of indices of unary operations). indicator is true if term starts with a variable
    and false if it starts with a constant. Index is index of variable or constant.
  *)
  let path_from_equation e =
    let rec loop acc = function
      | (Unary (op,t)) -> loop (op::acc) t
      | (Var v) -> (true, v, acc)
      | (Const c) -> (false, c, acc)
      | _ -> invalid_arg "path_from_equation: Binary operation." in
    match loop [] e with
      | (var, start, []) -> (var, start, None, [])
      | (var, start, os) -> (var, start, Some (List.nth os (List.length os - 1)), Util.init os) in

  (*
     Unary axioms in "normal form". Each side of the equation is a 4-tuple
     (is_variable, variable or const index, last operation or None, list of unary operations)
  *)
  let normal_axioms = List.map
    (fun (eq1, eq2) -> (path_from_equation eq1, path_from_equation eq2)) complicated in

  (* Main operation tables *)
  let unary_arr = Array.make_matrix lu n (-1) in

  (* Apply simple axioms *)
  List.iter
    (function
      | (Unary (op, Const c1), Const c2)
      | (Const c2, Unary (op, Const c1))
        -> unary_arr.(op).(c1) <- c2
      | _ -> invalid_arg "Something went terribly wrong in applying simple axioms.")
    simple ;

  (*
    Traces function applications in equation eq starting with start. If an unknown
    element comes up, it returns None.

    This can be improved. For example in a situation where we get the equation
    f(c) = d we can set f(c) immediately.
  *)
  let trace start eq =
    let rec result acc = function
      | [] -> Some acc
      | (x::xs) ->  let r = unary_arr.(x).(acc) in
                    if r = -1 then None else result r xs in
    result start eq in

  (*
    TODO: There are situations where we could deduce from axioms
    that an operation is bijection. E.g. f(f(x)) = x. It may be
    worth the trouble to implement.
  *)
  let actions_from_axiom axiom =
    let stack = Stack.create () in

    let undo id =
      while not (Stack.is_empty stack) && let (id', _, _) = Stack.top stack in id' = id do
        let (_, o, i) = Stack.pop stack in
        unary_arr.(o).(i) <- -1
      done in

    let trace_with cont id left i right j l1 l2 =
      match (trace i left, trace j right) with
        | (Some r1, Some r2) ->
          begin
            match (l1,l2) with
              | (None, None) -> r1 = r2
              | (None, Some op) ->
                if unary_arr.(op).(r2) = -1 then
                  begin
                    unary_arr.(op).(r2) <- r1 ;
                    Stack.push (id, op, r2) stack ;
                    cont id
                  end
                else
                  unary_arr.(op).(r2) = r1
              | (Some op, None) ->
                if unary_arr.(op).(r1) = -1 then
                  begin
                    unary_arr.(op).(r1) <- r2 ;
                    Stack.push (id, op, r1) stack ;
                    cont id
                  end
                else
                  unary_arr.(op).(r1) = r2
              | (Some op1, Some op2) ->
                let left = unary_arr.(op1).(r1) in
                let right = unary_arr.(op2).(r2) in
                if left = -1 && right <> -1 then
                  begin
                    unary_arr.(op1).(r1) <- right ;
                    Stack.push (id, op1, r1) stack ;
                    cont id
                  end
                else if left <> -1 && right = -1 then
                  begin
                    unary_arr.(op2).(r2) <- left ;
                    Stack.push (id, op2, r2) stack ;
                    cont id
                  end
                else
                  left = right
          end
        | _ -> true in

    match axiom with
      | ((true, id1, l1, left), (true, id2, l2, right)) when id1 = id2 ->
        let check_axiom cont id =
          let p = ref true in
          for i=0 to n-1 do
            p := !p && trace_with cont id left i right i l1 l2
          done ; !p in (check_axiom, undo)
      | ((true, id1, l1, left), (true, id2, l2, right)) ->
        let check_axiom cont id =
          let p = ref true in
          for i=0 to n-1 do
            for j=0 to n-1 do
              p := !p && trace_with cont id left i right j l1 l2
            done
          done ; !p in (check_axiom, undo)
      | ((true, id1, l1, left), (false, id2, l2, right))
      | ((false, id2, l2, right), (true, id1, l1, left)) ->
        let check_axiom cont id =
          let p = ref true in
          for i=0 to n-1 do
            p := !p && trace_with cont id left i right id2 l1 l2
          done ; !p in (check_axiom, undo)
      | ((_, id1, l1, left), (_, id2, l2, right)) ->
        let check_axiom cont id =
          trace_with cont id left id1 right id2 l1 l2  in (check_axiom, undo) in

  (*
     Check if any of the equations are violated by starting with
     every element and tracing function applications.
  *)
  let (dos, undos) = List.split (List.map actions_from_axiom normal_axioms) in

  let rec
      dodos id = List.for_all (fun f -> f dodos id) dos in
  let doundos id = List.iter (fun f -> f id) undos in

  (* Main loop. *)
  let rec
      gen_operation i = function
        | j when j = n && i < lu - 1 -> gen_operation (i+1) 0
        | j when j = n || i = lu -> gen_binary n lc lu lb binary_axioms unary_arr k
          (* || i = lu is necessary for when there aren't any unary operations *)
        | j when unary_arr.(i).(j) = -1 ->
          for k=0 to n-1 do
            unary_arr.(i).(j) <- k ;
            if dodos (i,j) then
              gen_operation i (j+1)
            ; doundos (i,j)
            ; unary_arr.(i).(j) <- -1 ;
          done
        | j -> gen_operation i (j+1)
  in gen_operation 0 0

(*
   Enumerate all algebras of a given size for the given theory
   and pass them to the given continuation.
*)
let enum n {signature={sig_const=const; sig_unary=unary; sig_binary=binary}; axioms=axioms} k =
  gen_unary n (List.length const) (List.length unary) (List.length binary) axioms k
