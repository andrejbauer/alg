open Type

exception Contradiction

exception Break

exception Undefined

(* ************************************************************** *)
(* Auxiliary functions for binary axioms. *)

(* Apply simple axioms to the binary operation tables. *)
let apply_simple_binary simple unary_arr binary_arr =
  (*
     Applies simple axioms to the main operation tables.
     If axioms aren't simple it fails miserably.
  *)
  let apply_simple axiom =
    let rec get_value = function
      | (Const c) -> c
      | (Unary (op,v)) -> unary_arr.(op).(get_value v)
      | _ -> invalid_arg "Ooops, binary operation or variable in apply_simple.get_value.
                          This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), Const c)
      | (Const c, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        if binary_arr.(op).(v1).(v2) <> -1 && binary_arr.(op).(v1).(v2) <> c then
          raise Contradiction
        else
          binary_arr.(op).(v1).(v2) <- c
      | _ -> invalid_arg "Not a simple binary axiom."
  in List.iter apply_simple simple

(* Apply one variable shallow axioms to the binary_arr operation tables. *)
let apply_one_var_shallow n one_var_shallow unary_arr binary_arr =
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
        if binary_arr.(op).(v1).(v2) <> -1 && binary_arr.(op).(v1).(v2) <> v3 then
          raise Contradiction
        else
          binary_arr.(op).(v1).(v2) <- v3
      | _ -> invalid_arg "not a legal axiom in apply_one_var"
  in
  for i=0 to n-1 do
    List.iter (fun x -> apply_one_var x i) one_var_shallow
  done

(*
  evaluate term in the context of vars. Raises Undefined if there is
  insufficient information to fully evaluate.
*)
let eval_eq unary_arr binary_arr vars =
  let rec eval_eq' = function
    | Const c -> c
    | Var v -> vars.(v)
    | Unary (op, t) ->
      begin match eval_eq' t with
        | -1 -> raise Undefined
        | v -> unary_arr.(op).(v)
      end
    | Binary (op, lt, rt) ->
      begin match eval_eq' lt with
        | -1 -> raise Undefined
        | lv ->
          begin match eval_eq' rt with
            | -1 -> raise Undefined
            | rv -> binary_arr.(op).(lv).(rv)
          end
      end in eval_eq'

let get_checks all_tuples unary_arr binary_arr zipped_axioms =
  (*
     Returns false if there is a conflict.
  *)
  let axiom_ok (num_vars, (left, right)) =
    let tuples = all_tuples.(num_vars) in
    let apply_to vars =
      try
        let a = eval_eq unary_arr binary_arr vars left in (* b is not evaluated if a is -1 *)
        a = -1 ||
            let b = eval_eq unary_arr binary_arr vars right in
            (b = -1 || a = b)
      with Undefined -> true
    in
      Util.array_for_all apply_to tuples in
  (*
    Checks if all axioms are still valid. This is for axioms that are not amenable.
    Amenable are checked immediately after adding each element.
  *)
  let check () = List.for_all axiom_ok zipped_axioms in check


(* ********************************************************************* *)
(*
   Auxiliary functions for computing actions from binary axioms and
   checking axiom validity after adding one element.
*)
let get_binary_actions n unary_arr binary_arr assoc amenable =
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
              let el1 = eval_eq unary_arr binary_arr vars l1 in
              let er1 = eval_eq unary_arr binary_arr vars r1 in
              let el2 = eval_eq unary_arr binary_arr vars l2 in
              let er2 = eval_eq unary_arr binary_arr vars r2 in
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
              let el2 = eval_eq unary_arr binary_arr vars l2 in
              let er2 = eval_eq unary_arr binary_arr vars r2 in
              let elt = eval_eq unary_arr binary_arr vars term in
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

  let doundos id = List.iter (fun f -> f id) undos in (dodos, doundos)

(* ******************************************************************************* *)
(* End of auxiliary functions for binary axioms *)

(* Main search function. *)
(*
  Generate binary operation tables. lc, lu and lb are numbers of constants,
  unary and binary operations. unary_arr is supposed to be a matrix
  of unary operations where each line is an operation, binary_arr is assumed to
  be a 3d array of binary operations, dodos and doundos are actions for
  amenable axioms, check checks if non-amenable axioms are still valid.
  k is the continuation.
*)
let gen_binary n lc lu lb dodos doundos unary_arr binary_arr check k =
  (* Main loop. *)
  (* o is index of operation, (i,j) current element *)
  let rec gen_operation o = function
    | _ when o = lb ->
        k { alg_size = n;
            alg_const = Array.init lc (fun k -> k);
            alg_unary = Util.matrix_copy unary_arr;
            alg_binary = Util.array3d_copy binary_arr
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
