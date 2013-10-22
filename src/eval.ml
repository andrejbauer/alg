open Algebra
open Theory

exception Undefined

(* Various evaluation functions. *)

(*
   Evaluate term in the context of vars, unary_arr and binary_arr.
   unary and binary operation arrays are assumed to be full so there
   should be no -1's anywhere.
*)
let eval_term {alg_const=c; alg_unary=u; alg_binary=b} vars t =
  let rec eval = function
    | Const v -> c.(v)
    | Elem e -> e
    | Var v -> vars.(v)
    | Unary (op, t) -> u.(op).(eval t)
    | Binary (op, t1, t2) -> b.(op).(eval t1).(eval t2)
  in
    eval t

let eval_term_partial {alg_const=const_arr; alg_unary=unary_arr; alg_binary=binary_arr} vars term =
  let rec eval_t_p = function
    | Const c ->
        begin match const_arr.(c) with
          | -1 -> raise Undefined
          | v -> v
        end
    | Elem e -> e
    | Var v -> vars.(v)
    | Unary (op, t) ->
      begin match eval_t_p t with
        | -1 -> raise Undefined
        | v -> unary_arr.(op).(v)
      end
    | Binary (op, lt, rt) ->
      begin match eval_t_p lt with
        | -1 -> raise Undefined
        | lv ->
          begin match eval_t_p rt with
            | -1 -> raise Undefined
            | rv -> binary_arr.(op).(lv).(rv)
          end
      end in 
  try match eval_t_p term with | -1 -> None | s -> Some s with Undefined -> None


(* Evaluate a formula. Returns None if undefined otherwise Some bool. *)
let eval_formula ({alg_predicates=ps; alg_relations=rs; alg_size=ns} as alg) vars f =
  let rec eval_formula' = function
    | True -> Some true
    | False -> Some false
    | Equal (t1,t2) -> 
      let r1 = eval_term_partial alg vars t1 in
      let r2 = eval_term_partial alg vars t2 in
        begin
          match r1, r2 with
            | (Some r1, Some r2) -> Some (r1 = r2)
            | _ -> None
        end
    | Forall (i,s,f) ->
      let b = ref true in
      let k = ref 0 in
        begin
          try 
            while !k < ns.(s) && !b do
              vars.(i) <- !k;
              (match eval_formula' f with
                | None -> raise Undefined
                | Some p -> b := p) ;
              incr k
            done ; Some !b
          with Undefined -> None
        end
    | Exists (i,s,f) ->
      let b = ref false in
      let k = ref 0 in
        begin
          try 
            while !k < ns.(s) && not !b do
              vars.(i) <- !k;
              (match eval_formula' f with
                | None -> raise Undefined
                | Some p -> b := p) ;
              incr k
            done ; Some !b
          with Undefined -> None
        end
    | And (f1,f2) ->
      begin
        match eval_formula' f1 with
          | None -> begin
            match eval_formula' f2 with 
              | Some false -> Some false
              | _ -> None
          end
          | Some false -> Some false
          | Some true -> eval_formula' f2
      end
    | Or (f1,f2) ->
      begin
        match eval_formula' f1 with
          | None -> begin
            match eval_formula' f2 with 
              | Some true -> Some true
              | _ -> None
          end
          | Some true -> Some true
          | Some false -> eval_formula' f2
      end
    | Imply (f1,f2) ->
      begin
        match eval_formula' f1 with
          | None -> begin
            match eval_formula' f2 with 
              | Some true -> Some true
              | _ -> None
          end
          | Some false -> Some true
          | Some true -> eval_formula' f2
      end
    | Iff (f1,f2) ->
      begin
        match eval_formula' f1 with
          | None -> None
          | a -> Some (a = eval_formula' f2)
      end
    | Not f ->
      begin
        match eval_formula' f with
          | None -> None
          | Some p -> Some (not p)
      end
    | Predicate (p,t) ->
      begin
        match eval_term_partial alg vars t with
          | None -> None
          | Some v -> let r = ps.(p).(v) in 
                        if r = -1 then None
                        else Some (if r = 1 then true else false)
      end
    | Relation (r,t1,t2) ->
      begin
        match eval_term_partial alg vars t1 with
          | None -> None
          | Some v1 -> begin
            match eval_term_partial alg vars t2 with
              | None -> None
              | Some v2 -> let rr = rs.(r).(v1).(v2) in 
                             if rr = -1 then None
                             else Some (if rr = 1 then true else false)
          end
      end in
    eval_formula' f
