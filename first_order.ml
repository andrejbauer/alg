open Type

(*
  Number of distinct variables in a formula.
*)
let num_vars f =
  let rec count_vars acc = function
    | Forall (i,f) -> count_vars (max acc i) f
    | Exists (i,f) -> count_vars (max acc i) f
    | And (f1,f2) | Or (f1,f2) | Implication (f1,f2) ->
      let maxl = count_vars acc f1 in
      count_vars maxl f2
    | Not f -> count_vars acc f
    | Equal _ | Not_Equal _ -> acc in
  1 + count_vars 0 f

(*
   Evaluate term in the context of vars, unary_arr and binary_arr.
   unary and binary operation arrays are assumed to be full so there
   should be no -1's anywhere.
*)
let eval_term vars unary_arr binary_arr term =
  let rec eval_term = function
    | Const c -> c
    | Var v -> vars.(v)
    | Unary (op, t) -> (List.assoc op unary_arr).(eval_term t)
    | Binary (op, lt, rt) ->
      (List.assoc op binary_arr).(eval_term lt).(eval_term rt) in
  eval_term term

(*
   Check if formula f is valid for algebra alg.
*)
let check_formula alg f =
  let n = alg.size in
  let nvars = num_vars f in
  let vars = Array.make nvars (-1) in
  let rec unwind = function
    | Forall (i,f) ->
      Util.for_all (fun j -> vars.(i) <- j; let r = unwind f in vars.(i) <- -1; r) 0 (n-1)
    | Exists (i,f) ->
      Util.exists (fun j -> vars.(i) <- j; let r = unwind f in vars.(i) <- -1; r) 0 (n-1)
    | And (f1,f2) ->
      unwind f1 && unwind f2
    | Or (f1,f2) ->
      unwind f1 || unwind f2
    | Implication (f1,f2) ->
      not (unwind f1) || unwind f2
    | Not f ->
      not (unwind f)
    | Equal (left, right) ->
      eval_term vars alg.unary alg.binary left = eval_term vars alg.unary alg.binary right
    | Not_Equal (left, right) ->
      eval_term vars alg.unary alg.binary left <> eval_term vars alg.unary alg.binary right in
  unwind f

let check_formulas theory alg =
  match theory.formulas with
    | None -> true
    | Some fs -> List.for_all (check_formula alg) fs
