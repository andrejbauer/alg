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
          | _ -> failwith "Binary operation creeped in part_one_binary.is_simple."
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
  List of distinct variables of an axiom.
  Obviously quadratic in number of variables. TODO
*)
let dist_vars (left, right) =
  let rec
      eq_vars acc = function
        | Const _ -> acc
        | Var v -> if List.mem v acc then acc else (v :: acc)
        | Binary (_,t1,t2) -> let lv = eq_vars acc t1 in
                              eq_vars lv t2
        | Unary (_,t) -> eq_vars acc t in
  let lv = eq_vars [] left in eq_vars lv right

(*
  Number of distinct variables in an axiom.
  Could also look for maximum variable index.
*)
let num_dist_vars a = List.length (dist_vars a)

let partition_shallow axioms = 
  let is_shallow = function
    | (Binary (_,(Var _), (Var _))) 
(* TODO    | (Binary (_,(Var _), (Const _))) 
    | (Binary (_,(Const _), (Var _)))  *) -> true
    | _ -> false (* TODO: Think of a simple way to include unary operations. *) in 
  List.partition (fun (left, right) -> is_shallow left && is_shallow right) axioms
  

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
      | _ -> failwith "Ooops, binary operation or variable in apply_simple.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), Const c)
      | (Const c, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        binary_arr.(op).(v1).(v2) <- c
      | _ -> failwith "Not a simple binary axiom."
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
      | _ -> failwith "Ooops, binary operation in apply_one_var.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), t3)
      | (t3, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        let v3 = get_value t3 in
        binary_arr.(op).(v1).(v2) <- v3
      | _ -> failwith "not a legal axiom in apply_one_var"
  in
  for i=0 to n-1 do
    List.iter (fun x -> apply_one_var x i) one_var_shallow
  done ;

  (* Shallow axioms with no more than two variables. These are the easiest. *)
  (* Zipped means in the form (number of distinct variables, axioms) *)
  let (shallow, assoc, zipped_axioms) = 
    let (assoc, rest) = partition_assoc left in
    let (sh, za) = partition_shallow rest in
    let shz = List.map (fun a -> (num_dist_vars a, a)) sh in
    let zaz = List.map (fun a -> (num_dist_vars a, a)) za in
    let (good, bad) = List.partition (fun (nd,_) -> nd <= 2) shz in
    (* Check axioms with fewer free variables first. *)
    (List.map snd good, assoc, List.sort (fun (n,_) (m,_) -> compare n m) (bad @ zaz)) in
  Printf.printf "%d\n" (List.length zipped_axioms) ;
  let max_vars = List.fold_left max 0 (List.map num_dist_vars left) in 

  (* This could potentially gobble up memory. TODO *)
  let all_tuples = Array.init (max_vars + 1) (fun i -> ntuples n i) in

  (*
     Returns false if there is a conflict.
  *)
  let axiom_ok (num_vars, (left, right)) =
    let tuples = all_tuples.(num_vars) in
    let apply_to i =
      let rec eval_eq = function
        | Const c -> c
        | Var v -> i.(v)
        | Unary (op, t) ->
            begin match eval_eq t with
              | -1 -> raise Undefined
              | v -> unary_arr.(op).(v)
            end
        | Binary (op, lt, rt) ->
            begin match eval_eq lt with
              | -1 -> raise Undefined
              | lv ->
                  begin match eval_eq rt with
                    | -1 -> raise Undefined
                    | rv -> binary_arr.(op).(lv).(rv)
                  end
            end
      in
        try
          let a = eval_eq left in (* b is not evaluated if a is -1 *)
            a = -1 || 
              let b = eval_eq right in
              (b = -1 || a = b)
        with Undefined -> true
    in
      Util.array_for_all apply_to tuples
  in

  (*
    Checks if all axioms are still valid.
    TODO: Needlessly slow.
  *)
  let check () = List.for_all axiom_ok zipped_axioms in
  
  let actions_from_shallow = function
    | (Binary (opl, Var vl1, Var vl2), Binary (opr, Var vr1, Var vr2)) -> 
    (* x is the index in the stack table, o index of operation. We just set (i,j) to k in o. *)
    let stack = Stack.create () in 
    let f id o i j = 
      if o = opl then
        begin
          if vl1 <> vl2 then (* We have two distinct variables *)
            begin 
              let left = if vr1 = vl1 then i else j in
              let right = if vr2 = vl2 then j else i in
              if binary_arr.(opr).(left).(right) = -1 then
                begin
                  binary_arr.(opr).(left).(right) <- binary_arr.(opl).(i).(j) ;
                  Stack.push (id, opr, left, right) stack ; true
                end
              else binary_arr.(opr).(left).(right) = binary_arr.(opl).(i).(j)
            end
          else true (* TODO There is only one variable on the left side of equation *)
        end
      else 
        if o = opr then
          begin
            if vr1 <> vr2 then (* We have two distinct variables *)
              begin 
                let left = if vl1 = vr1 then i else j in
                let right = if vl2 = vr2 then j else i in
                if binary_arr.(opl).(left).(right) = -1 then
                  begin
                    binary_arr.(opl).(left).(right) <- binary_arr.(opr).(i).(j) ;
                    Stack.push (id, opl, left, right) stack ; true
                  end
                else binary_arr.(opl).(left).(right) = binary_arr.(opr).(i).(j)
              end
            else true (* TODO There is only one variable on the left side of equation *)
          end 
        else true
    in
    let undo id = 
      while not (Stack.is_empty stack) && let (id', _, _,_) = Stack.top stack in id = id' do
        let (_, op, left, right) = Stack.pop stack in
        binary_arr.(op).(left).(right) <- -1
      done in (f, undo)
    | _ -> failwith "actions_from_shallow not yet implemented" in

  let actions_from_assoc = function
    | (Binary (op1, Binary (op2, Var a1, Var b1), Var c1), Binary (op3, Var a2, Binary (op4, Var b2, Var c2)))
    | (Binary (op3, Var a2, Binary (op4, Var b2, Var c2)), Binary (op1, Binary (op2, Var a1, Var b1), Var c1))
        when op1 = op2 && op2 = op3 && op3 = op4 && a1 = a2 && b1 = b2 && c1 = c2 ->
      let stack = Stack.create () in 
      let rec f id o i j = 
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
                      if not (f id o i bc) then
                        raise Break
                    end
                  else if ab_c = -1 && a_bc <> -1 then
                    begin
                      binary_arr.(o).(ab).(k) <- a_bc ;
                      Stack.push (id, o,ab,k) stack ;
                      if not (f id o ab k) then
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
                      if not (f id o k bc) then
                        raise Break
                    end
                  else if ab_c = -1 && a_bc <> -1 then
                    begin
                      binary_arr.(o).(ab).(j) <- a_bc ;
                      Stack.push (id, o,ab,j) stack ;
                      if not (f id o ab j) then
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
                            if not (f id o a bc) then
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
                            if not (f id o ab c) then
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
    | _ -> failwith "actions_from_assoc axiom given is not associativity" in


  let (dos, undos) = List.split ((List.map actions_from_shallow shallow) @ 
                                    List.map actions_from_assoc assoc) in

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
        if List.for_all (fun f -> f (o,i,j) o i j) dos && check () then
          gen_operation o (i,j+1)
        ; List.iter (fun f -> f (o,i,j)) undos
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
     TODO: The ones of the form f_1(...(f_n(c))) = d for c and d constants create
     connections between tables. If c and d are variables this is the same as
     n^2 pairs of constant.
  *)
  let (simple, complicated) = part_unary_axioms unary_axioms in
  (*
     Preliminary version. Equation consists only of unary operations and variables.
     TODO: If we don't require bijections then f_1(...f_n(x)...) = c are also valid.
  *)
  let path_from_equation e =
    let rec loop acc = function
      | (Unary (op,t)) -> loop (op::acc) t
      | (Var v) -> (true, v, acc)
      | (Const c) -> (false, c, acc)
      | _ -> failwith "path_from_equation: Not yet implemented."
    in loop [] e in

  (* 
     Unary axioms in "normal form". Each side of the equation is a triple 
     (is_variable, variable or const index, list of unary operations 
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
      | _ -> failwith "Something went terribly wrong!")
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

  (* Check if a particular axiom is violated. *)
  let check_axiom = function 
    | ((true, id1, left), (true, id2, right)) when id1 = id2 -> 
      let p = ref true in
      for i=0 to n-1 do
        if !p then 
          match (trace i left, trace i right) with
            | (Some r1, Some r2) -> p := r1 = r2
            | _ -> ()
      done ; !p
    | ((true, id1, left), (true, id2, right)) -> 
      let p = ref true in
      for i=0 to n-1 do
        for j=0 to n-1 do
          if !p then 
            match (trace i left, trace j right) with
              | (Some r1, Some r2) -> p := r1 = r2
              | _ -> ()
        done
      done ; !p
    | ((true, id1, left), (false, id2, right))
    | ((false, id2, right), (true, id1, left)) -> 
      let p = ref true in
      for i=0 to n-1 do
        if !p then 
          match (trace i left, trace id2 right) with
            | (Some r1, Some r2) -> p := r1 = r2
            | _ -> ()
      done ; !p
    | ((_, id1, left), (_, id2, right)) -> 
        match (trace id1 left, trace id2 right) with
          | (Some r1, Some r2) -> r1 = r2
          | _ -> true  in
  (* 
     Check if any of the equations are violated by starting with
     every element and tracing function applications.
  *)
  let check () = List.for_all check_axiom normal_axioms in 

  (*
     Main loop. Baseline.
  *)
  let rec
      gen_operation i = function
        | j when j = n && i < lu - 1 -> gen_operation (i+1) 0
        | j when j = n || i = lu -> gen_binary n lc lu lb binary_axioms unary_arr k
          (* || i = lu is necessary for when there aren't any unary operations *)
        | j when unary_arr.(i).(j) = -1 ->
          for k=0 to n-1 do
            unary_arr.(i).(j) <- k ;
            if check () then
              gen_operation i (j+1)
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
