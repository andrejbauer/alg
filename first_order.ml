open Type

(*
   Evaluate term in the context of vars, unary_arr and binary_arr.
   unary and binary operation arrays are assumed to be full so there
   should be no -1's anywhere.
*)
let eval_term vars unary_arr binary_arr term =
  let rec eval = function
    | Const c -> c
    | Var v -> vars.(v)
    | Unary (op, t) -> unary_arr.(op).(eval t)
    | Binary (op, t1, t2) -> binary_arr.(op).(eval t1).(eval t2) in
  eval term

let rec max_var = function
  | True -> -1
  | False -> -1
  | Equal (t1, t2) ->
      let rec max_var_term = function
        | Var k -> k
        | Const _ -> -1
        | Unary (_, t) -> max_var_term t
        | Binary (_, t1, t2) -> max (max_var_term t1) (max_var_term t2)
      in
        max (max_var_term t1) (max_var_term t2)
  | Forall (x, f) | Exists (x, f) -> max x (max_var f)
  | And (f1, f2) | Or (f1, f2) | Imply (f1, f2) | Iff (f1, f2) -> max (max_var f1) (max_var f2)
  | Not f -> max_var f

(*
   Check if formula f is valid for algebra alg.
*)
let check_formula alg f =
  let n = alg.alg_size in
  let nvars = max_var f in
  let vars = Array.make nvars (-1) in
  let rec eval = function
    | False -> false
    | True -> true
    | Forall (i,f) ->
      Util.for_all (fun j -> vars.(i) <- j; let r = eval f in vars.(i) <- -1; r) 0 (n-1)
    | Exists (i,f) ->
      Util.exists (fun j -> vars.(i) <- j; let r = eval f in vars.(i) <- -1; r) 0 (n-1)
    | And (f1,f2) ->
      eval f1 && eval f2
    | Or (f1,f2) ->
      eval f1 || eval f2
    | Imply (f1,f2) ->
      eval f1 <= eval f2
    | Iff (f1, f2) ->
      eval f1 = eval f2
    | Not f ->
      not (eval f)
    | Equal (t1, t2) ->
      eval_term vars alg.alg_unary alg.alg_binary t1 = eval_term vars alg.alg_unary alg.alg_binary t2
  in
    eval f

let check_axioms theory alg =
  List.for_all (check_formula alg) theory.th_axioms
