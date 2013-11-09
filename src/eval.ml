(** Evaluation functions *)

(* Evaluate a term in the context of varsand operations, which are assumed to be fully
   defined so there should be no -1's anywhere. *)
let eval_term {Algebra.alg_const=c; Algebra.alg_unary=u; Algebra.alg_binary=b} vars =
  let rec eval = function
    | Syntax.Const v -> c.(v)
    | Syntax.Elem e -> e
    | Syntax.Var v -> vars.(v)
    | Syntax.Unary (op, t) -> u.(op).(eval t)
    | Syntax.Binary (op, t1, t2) -> b.(op).(eval t1).(eval t2)
  in
    eval

(* Evaluate a formula, assuming all operations are fully defined. *)
let eval_formula
    ({Algebra.alg_size=size;
      Algebra.alg_predicate=predicate;
      Algebra.alg_relation=relation} as alg)
    vars =
  let {Algebra.alg_size=size} = alg in
  let rec eval = function
    | Syntax.False -> false
    | Syntax.True -> true
    | Syntax.Equal (t1, t2) -> eval_term alg vars t1 = eval_term alg vars t2
    | Syntax.Predicate (k, t) -> predicate.(k).(eval_term alg vars t) = 1
    | Syntax.Relation (k, t1, t2) -> relation.(k).(eval_term alg vars t1).(eval_term alg vars t2) = 1
    | Syntax.Not f -> not (eval f)
    | Syntax.And (f1,f2) -> eval f1 && eval f2
    | Syntax.Or (f1,f2) -> eval f1 || eval f2
    | Syntax.Imply (f1,f2) -> eval f1 <= eval f2
    | Syntax.Iff (f1, f2) -> eval f1 = eval f2
    | Syntax.Forall (i,s,f) ->
      let n = size.(s) in
      let b = ref true in
        vars.(i) <- 0 ;
        while !b && vars.(i) < n do
          b := eval f ;
          vars.(i) <- vars.(i) + 1
        done ;
        !b
    | Syntax.Exists (i,s,f) ->
      let n = size.(s) in
      let b = ref true in
        vars.(i) <- 0 ;
        while not !b && vars.(i) < n do
          b := eval f ;
          vars.(i) <- vars.(i) + 1
        done ;
        !b
  in
    eval

(* Evaluate a term where some operations may still be undefined. *)
let eval_term_partial
    {Algebra.alg_const=const; Algebra.alg_unary=unary; Algebra.alg_binary=binary} vars =
  let rec eval = function
    | Syntax.Const c ->
        begin match const.(c) with
          | -1 -> None
          | v -> Some v
        end
    | Syntax.Elem e -> Some e
    | Syntax.Var v -> Some (vars.(v))
    | Syntax.Unary (op, t) ->
      begin match eval t with
        | None -> None
        | Some v -> 
          begin match unary.(op).(v) with
            | (-1) -> None
            | w -> Some w
          end
      end
    | Syntax.Binary (op, t1, t2) ->
      begin match eval t1 with
        | None -> None
        | Some v1 ->
          begin match eval t2 with
            | None -> None
            | Some v2 ->
              begin match binary.(op).(v1).(v2) with
                | (-1) -> None
                | w -> Some w
              end
          end
      end in 
    eval

(* Evaluate a formula, with possibly undefined value.
   Returns None if undefined otherwise Some bool.*)
let eval_formula_partial
    ({Algebra.alg_predicate=ps; Algebra.alg_relation=rs; Algebra.alg_size=size} as alg) vars f =
  let rec eval = function
    | Syntax.True -> Some true
    | Syntax.False -> Some false
    | Syntax.Equal (t1,t2) ->
      begin match eval_term_partial alg vars t1 with
        | None -> None
        | Some v1 ->
          begin match eval_term_partial alg vars t2 with
            | None -> None
            | Some v2 -> Some (v1 = v2)
          end
      end
    | Syntax.Forall (i,s,f) ->
      let n = size.(s) in
      let b = ref (Some true) in
        vars.(i) <- 0 ;
        while !b <> (Some false) && vars.(i) < n do
          b := (match eval f with None -> None | Some false -> Some false | Some true -> !b) ;
            vars.(i) <- vars.(i) + 1
        done ;
        !b
    | Syntax.Exists (i,s,f) ->
      let n = size.(s) in
      let b = ref (Some false) in
        vars.(i) <- 0 ;
        while !b <> (Some true) && vars.(i) < n do
          b := (match eval f with None -> None | Some true -> Some true | Some false -> !b) ;
          vars.(i) <- vars.(i) + 1
        done ;
        !b
    | Syntax.And (f1,f2) ->
      begin match eval f1 with
        | None ->
          begin match eval f2 with 
            | Some false -> Some false
            | Some true | None -> None
          end
        | Some false -> Some false
        | Some true -> eval f2
      end
    | Syntax.Or (f1,f2) ->
      begin match eval f1 with
        | None ->
          begin match eval f2 with 
            | Some true -> Some true
            | Some false | None -> None
        end
        | Some true -> Some true
        | Some false -> eval f2
    end
    | Syntax.Imply (f1,f2) ->
      begin match eval f1 with
        | None ->
          begin match eval f2 with 
            | Some true -> Some true
            | Some false | None -> None
          end
        | Some false -> Some true
        | Some true -> eval f2
      end
    | Syntax.Iff (f1,f2) ->
      begin match eval f1 with
        | None -> None
        | a -> Some (a = eval f2)
      end
    | Syntax.Not f ->
      begin match eval f with
        | None -> None
        | Some p -> Some (not p)
      end
    | Syntax.Predicate (p,t) ->
      begin match eval_term_partial alg vars t with
        | None -> None
        | Some v ->
          let r = ps.(p).(v) in 
            if r = -1 then None
            else Some (r = 1)
      end
    | Syntax.Relation (r,t1,t2) ->
      begin match eval_term_partial alg vars t1 with
        | None -> None
        | Some v1 ->
          begin match eval_term_partial alg vars t2 with
            | None -> None
            | Some v2 -> let rr = rs.(r).(v1).(v2) in 
                         if rr = -1 then None
                         else Some (rr = 1)
          end
      end
  in
    eval f
                          
let eval_axioms {Syntax.th_axiom=lst} alg =
  List.for_all (fun (vars, f) -> eval_formula alg vars f) lst
