open Type

(*
   Evaluate term in the context of vars, unary_arr and binary_arr.
   unary and binary operation arrays are assumed to be full so there
   should be no -1's anywhere.
*)
let eval_term {alg_const=c; alg_unary=u; alg_binary=b} vars t =
  let rec eval = function
    | Const v -> c.(v)
    | Var v -> vars.(v)
    | Unary (op, t) -> u.(op).(eval t)
    | Binary (op, t1, t2) -> b.(op).(eval t1).(eval t2)
  in
    eval t

(* Check if formula f is valid for algebra alg. *)
let check_formula alg (vars,f) =
  let n = alg.alg_size in
  let rec eval = function
    | False -> false
    | True -> true
    | Equal (t1, t2) -> eval_term alg vars t1 = eval_term alg vars t2
    | Predicate (k, t) -> alg.alg_predicates.(k).(eval_term alg vars t) = 1
    | Relation (k, t1, t2) ->
        alg.alg_relations.(k).(eval_term alg vars t1).(eval_term alg vars t2) = 1
    | Not f -> not (eval f)
    | And (f1,f2) -> eval f1 && eval f2
    | Or (f1,f2) -> eval f1 || eval f2
    | Imply (f1,f2) -> eval f1 <= eval f2
    | Iff (f1, f2) -> eval f1 = eval f2
    | Forall (i,f) ->
        let b = ref true in
        let v = ref 0 in
          while !b && !v < n do
            vars.(i) <- !v ;
            b := eval f ;
            incr v
          done ;
          !b
    | Exists (i,f) ->
        let b = ref false in
        let v = ref 0 in
          while not !b && !v < n do
            vars.(i) <- !v ;
            b := eval f ;
            incr v
          done ;
          !b
  in
    eval f

let check_axioms theory alg =
  List.for_all (check_formula alg) theory.th_axioms
