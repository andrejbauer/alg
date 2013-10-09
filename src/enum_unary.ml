open Theory
open Algebra

(* ******************************************************************************* *)
(* Auxiliary functions for unary axioms. *)

(* Apply simple axioms to operation tables unary_arr *)
let apply_simple simple {alg_unary=unary_arr} =
  (* Apply simple axioms *)
  List.iter
    (function
      | (Unary (op, Const c1), Const c2)
      | (Const c2, Unary (op, Const c1)) ->
          if unary_arr.(op).(c1) <> -1 && unary_arr.(op).(c1) <> c2
          then raise InconsistentAxioms
          else unary_arr.(op).(c1) <- c2
      | _ -> invalid_arg "Not a simple axiom in apply_simple.")
    simple

(* Get do and undo actions from axioms in normal form for use in main loop of gen_unary. *)
let get_unary_actions normal_axioms {alg_size=n; alg_unary=unary_arr} =
  (*
    Traces function applications in equation eq starting with start. If an unknown
    element comes up, it returns None.
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
      while not (Stack.is_empty stack) && (let (id', _, _) = Stack.top stack in id' = id) do
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
  (dodos, doundos)


(* Get axioms in normal form from "complicated" axioms. *)
let get_normal_axioms complicated =
  (*
    Equation must not contain any binary operations.
    path_from_equation returns a 4-tuple (indicator, index, index of last operation,
    list of indices of unary operations). indicator is true if term starts with a variable
    and false if it starts with a constant. Index is index of variable or constant.
  *)
  let path_from_equation e =
    (* TODO this function must be a kludge, get rid of it. *)
    let rec init = function
      | [] -> []
      | [_] -> []
      | x :: xs -> x :: init xs
    in
    let rec loop acc = function
      | (Unary (op,t)) -> loop (op::acc) t
      | (Var v) -> (true, v, acc)
      | (Const c) -> (false, c, acc)
      | _ -> invalid_arg "path_from_equation: Binary operation." in
    match loop [] e with
      | (var, start, []) -> (var, start, None, [])
      | (var, start, os) -> (var, start, Some (List.nth os (List.length os - 1)), init os) in

  (*
     Unary axioms in "normal form". Each side of the equation is a 4-tuple
     (is_variable, variable or const index, last operation or None, list of unary operations)
  *)
  List.map (fun (eq1, eq2) -> (path_from_equation eq1, path_from_equation eq2)) complicated

(* ************************************************************************** *)
(* End of auxiliary functions for unary axioms. *)


(* ************************************************************************** *)
(* Main search functions. *)

(*
  Generate unary operation tables. lc, lu and lb are numbers of constants,
  unary and binary operations.
*)
let gen_unary th dodos doundos {alg_size=n; alg_unary=unary_arr} k =
  let lu = Array.length th.th_unary in
  (* Main loop. *)
  let rec
      gen_operation i = function
        | j when j = n && i < lu - 1 -> gen_operation (i+1) 0
        | j when j = n || i = lu -> k ()
          (* || i = lu is necessary for when there aren't any unary operations *)
        | j when unary_arr.(i).(j) = -1 ->
          for k = 0 to n-1 do
            unary_arr.(i).(j) <- k ;
            if dodos (i,j) then gen_operation i (j+1) ;
            doundos (i,j) ;
            unary_arr.(i).(j) <- -1 ;
          done
        | j -> gen_operation i (j+1)
  in gen_operation 0 0

