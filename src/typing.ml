(* Type checking and conversion from [Input] to [Syntax]. *)

type env = {
  const : (Input.operation * (Syntax.index * Syntax.sort)) list ;
  unary : (Input.operation * (Syntax.index * (Syntax.sort * Syntax.sort))) list ;
  binary : (Input.operation * (Syntax.index * (Syntax.sort * Syntax.sort * Syntax.sort))) list ;
  predicate : (Input.operation * (Syntax.index * Syntax.sort)) list ;
  relation : (Input.operation * (Syntax.index * (Syntax.sort * Syntax.sort))) list ;
  axiom : Syntax.ctx_formula list
}

let empty_env = {
  const = [];
  unary = [];
  binary = [];
  predicate = [];
  relation = [];
  axiom = []
}

let fresh lst = 1 + List.fold_left (fun m (_,k) -> max m k) (-1) lst

let lookup_var xs x = Util.lookup x xs

let lookup_sort {sort=es} s = Util.lookup s es

let lookup_const {const=ec} x = Util.lookup x ec

let lookup_unary {unary=eu} x = Util.lookup x eu

let lookup_binary {binary=eb} x = Util.lookup x eb

let lookup_predicate {predicate=ep} x = Util.lookup x ep

let lookup_relation {relation=er} x = Util.lookup x er

let lookup_any env n =
  match lookup_sort env n with
    | Some _ -> Some "sort"
    | None ->
      begin match lookup_const env n with
        | Some _ -> Some "constant"
        | None ->
          begin   match lookup_unary env n with
            | Some _ -> Some "unary operation"
            | None ->
              begin match lookup_binary env n with
                | Some _ -> Some "binary operation"
                | None ->
                  begin match lookup_predicate env n with
                    | Some _ -> Some "predicate"
                    | None ->
                      begin match lookup_relation env n with
                        | Some _ -> Some "relation"
                        | None -> None
                      end
                  end
              end
          end
      end

let check_duplicate env loc n =
  match lookup_any env n with
    | None -> ()
    | Some s -> Error.typing ~loc "duplicate declaration, %s is already declared to be a %s" n s

let extend_var xs x sopt = (x, (fresh env.var, ref sopt)) :: env.var

let extend_sort env s = 
  check_duplicate env s ;
  { env with const = (s, fresh env.sort) :: env.sort }

let extend_const env c s = 
  check_duplicate env c ;
  { env with const = (c, (fresh env.const, s)) :: env.const }

let extend_unary env u s1 s2 = 
  check_duplicate env xu;
  { env with unary = (u, (fresh env.unary, s1, s2)) :: env.unary }

let extend_binary env b s1 s2 s3 = 
  check_duplicate env b ;
  { env with binary = (b, (fresh env.binary, s1, s2, s3)) :: env.binary }

let extend_predicate env p s = 
  check_duplicate env p ;
  { env with predicate = (p, (fresh env.predicate, s)) :: env.predicate }

let extend_relation env r s1 s2 = 
  check_duplicate env r ;
  { env with relation = (r, (fresh env.relation, s1, s2)) :: env.relation }

let extend_axiom env f =
  { env with axiom = f :: env.axiom }

(* let is_op {const=ec; unary=eu; binary=eb} x = *)
(*   List.mem_assoc x ec || List.mem_assoc x eu || List.mem_assoc x eb *)

(* The free variables of a term, without repetitions. *)
let rec fv_term env (t, loc) =
  match t with
    | Input.Var x -> if is_op env x then [] else [x]
    | Input.UnaryOp (_, t) -> fv_term env t
    | Input.BinaryOp (_, t1, t2) -> Util.union (fv_term env t1) (fv_term env t2)

(* The free variables of a formula, without repetitions. *)
let rec fv_formula env (f, loc) =
  match f with
    | Input.False -> []
    | Input.True -> []
    | Input.Equal (t1, t2)
    | Input.NotEqual (t1, t2) -> Util.union (fv_term env t1) (fv_term env t2)
    | Input.UnaryPr (_, t) -> fv_term env t
    | Input.BinaryPr (_, t1, t2) -> Util.union (fv_term env t1) (fv_term env t2)
    | Input.Not f -> fv_formula env f
    | Input.And (f1, f2)
    | Input.Or (f1, f2)
    | Input.Imply (f1, f2)
    | Input.Iff (f1, f2) -> Util.union (fv_formula env f1) (fv_formula env f2)
    | Input.Forall (xs, f) | Input.Exists (xs, f) -> Util.remove_many xs (fv_formula env f)

let check_sort loc s1 s2 =
  if s1 <> s2 then
    Error.typing ~loc "this expression has sort %s but should have sort %s" s1 s2

let term env vars =
  let rec term s (t, loc) =
    match t with

      | Input.Ident x ->
        begin match lookup_var vars x with
          | Some (k, r) -> 
            begin match !r with
              | None -> r := Some s ; Syntax.Var k
              | Some s' -> check_sort loc s' s ; Syntax.Var k
          end
        | None ->
          begin match lookup_const env x with
            | Some (k, s') -> check_sort loc s' s ; Syntax.Const k
            | None -> Error.typing_error ~loc "unknown variable or constant %s" x
          end
        end

      | Input.UnaryOp (op, t) ->
        begin match lookup_unary env op with
          | Some (u, s1, s2) -> check_sort loc s2 s ; Syntax.Unary (u, term s1 t)
          | None -> Error.typing_error ~loc "unknown unary operator %s" op
        end

      | Input.BinaryOp (op, t1, t2) ->
        begin match lookup_binary env op with
          | Some (b, s1, s2, s3) -> check_sort loc s3 s ; Syntax.Binary (b, term s1 t1, term s2 t2)
          | None -> Error.typing_error ~loc "unkown binary operator %s" op
        end
  in
    term

let formula env f =
  let infer_sort vars (t, loc) =
    match t with
      | Input.Ident x ->
        begin match lookup_const env x with
          | Some (_, s) -> Some s
          | None -> None
            begin match lookup_var env x with
              | Some (_, s) -> Some s
              | None -> None
            end
      end
      | Input.UnaryOp (op, _) ->
        begin match lookup_unary env op with
          | Some (_, _, s) -> Some s
          | None -> None
        end
      | Input.BinaryOp (op, _, _) ->
        begin match lookup_binary env op with
          | Some (_, _, _, s) -> Some s
          | None -> None
        end
  in

  (* return the formula and a list of free variables with their sorts *)
  let rec formula vars (f,loc) =
    match f with
      | Input.True -> Syntax.True

      | Input.False -> Syntax.False

      | Input.UnaryPr (op, t) ->
        begin match lookup_predicate env op with
          | Some (u, s) -> Syntax.Predicate (u, term env vars s t)
          | None -> 
            begin match lookup_any env op with
              | None -> Error.typing_error ~loc "unknown predicate %s" op
              | Some n -> Error.typing_error ~loc "%s is a %s but is used as a predicate" op n
            end
        end

      | Input.BinaryPr (op, t1, t2) ->
        begin match lookup_relation env op with
          | Some (b, s1, s2) -> Syntax.Relation (b, term env vars s1 t1, term env vars s2 t2)
          | None ->
            begin match lookup_any env op with
              | None -> Error.typing_error ~loc "unknown relation %s" op
              | Some n -> Error.typing_error ~loc "%s is a %s but is used as a relation" op n
            end
        end

      | Input.Equal (t1, t2) -> 
        let s =
          begin match infer_sort vars t1, infer_sort vars t2 with
            | Some s, _ -> s
            | None, Some s -> s
            | None, None -> Error.typing ~loc:(snd t1) "this term has an unknown sort"
          end
        in
          Syntax.Equal (term env vars s t1, term env vars s t2)

      | Input.NotEqual (t1, t2) ->
        let f = formula env (Equal (t1, t2), loc) in
          Syntax.Not f

      | Input.And (f1,f2) -> Syntax.And (formula vars f1, formula vars f2)

      | Input.Or (f1,f2) -> Syntax.Or (formula vars f1, formula vars f2)

      | Input.Imply (f1,f2) -> Syntax.Imply (formula vars f1, formula vars f2)

      | Input.Iff (f1,f2) -> Syntax.Iff (formula vars f1, formula vars f2)

      | Input.Not f -> Syntax.Not (formula vars f)

      | Input.Forall ([], f) -> formula vars f
      | Input.Forall (([], _) :: lst, f) -> formula vars (Input.Forall (lst, f))
      | Input.Forall ((x::xs, sopt) :: lst, f) ->
        let env = extend_var vars x sopt in
        let f = formula vars (Input.Forall ((xs, s) :: lst, f)) in
          begin match lookup_var vars x with
            | None -> Error.internal ~loc "Typing.formula in Forall"
            | Some r ->
              begin match !r with
                | None -> Error.typing ~loc "cannot infer the sort of %s" x
                | Some (k, s) -> Syntax.Forall (k, s, f)
              end
          end

      | Input.Exists ([], f) -> formula vars f
      | Input.Exists (([], _) :: lst, f) -> formula vars (Input.Exists (lst, f))
      | Input.Exists ((x::xs, sopt) :: lst, f) ->
        let env = extend_var vars x sopt in
        let f = formula vars (Input.Exists ((xs, s) :: lst, f)) in
          begin match lookup_var env x with
            | None -> Error.internal ~loc "Typing.formula in Exists"
            | Some r ->
              begin match !r with
                | None -> Error.typing ~loc "cannot infer the sort of %s" x
                | Some (k, s) -> Syntax.Exists (k, s, f)
              end
          end

  in
  let loc = snd f in
  let xs = fv_formula env f in
  let f = Input.Forall ((xs, None), f), loc in
    formula [] f

let rec as_equation = function
  | True | False | Or _ | And _ | Imply _ | Iff _ | Not _ | Exists _ -> None
  | Forall (x, s, f) ->
    begin match as_equation f with
      | None -> None
      | Some (xs, t1, t2) -> Some ((x,s) :: xs, t1, t2)
    end
  | Equation (t1, t2) -> Some ([], t1, t2)

let entry env (ent,loc) =
  match ent with
    | Syntax.Sort ss -> List.fold_left extend_sort env ss
    | Syntax.Constant (cs, s) ->
      begin match lookup_sort env s with
        | None -> Error.typing_error ~loc "Unknown sort %s" s
        | Some s -> List.fold_left (fun env c -> extend_const env c s) env cs
      end
    | Syntax.Unary (us, s1, s2) ->
      begin match lookup_sort env s1 with
        | None -> Error.typing_error ~loc "Unknown sort %s" s1
        | Some s1 ->
          begin match lookup_sort env s2 with
            | None -> Error.typing ~loc "Uknown sort %s" s2
            | Some s2 -> List.fold_left (fun env u -> extend_unary env u s1 s2) env us
          end
      end
    | Syntax.Binary (bs, s1, s2, s3) ->
      begin match lookup_sort env s1 with
        | None -> Error.typing_error ~loc "Unknown sort %s" s1
        | Some s1 ->
          begin match lookup_sort env s2 with
            | None -> Error.typing ~loc "Uknown sort %s" s2
            | Some s2 ->
              begin match lookup_sort env s3 with
                | None -> Error.typing ~loc "Uknown sort %s" s3
                | Some s3 -> List.fold_left (fun env b -> extend_binary env b s1 s2 s3) env bs
              end
          end
      end
    | Syntax.Predicate (ps, s) ->
      begin match lookup_sort env s with
        | None -> Error.typing_error ~loc "Unknown sort %s" s
        | Some s -> List.fold_left (fun env p -> extend_predicate env p s) env ps
      end
    | Syntax.Relation (rs, s1, s2) ->
      begin match lookup_sort env s1 with
        | None -> Error.typing_error ~loc "Unknown sort %s" s1
        | Some s1 ->
          begin match lookup_sort env s2 with
            | None -> Error.typing ~loc "Uknown sort %s" s2
            | Some s2 -> List.fold_left (fun env r -> extend_relation env r s1 s2) env rs
          end
      end
    | Syntax.Axiom (_, f) ->
      let f = formula env f in
        begin match as_equation f with
          | Some (xs, t1, t2) -> extend_equation env (xs, t1, t2)
          | None -> extend_axiom env f
        end

let theory {Input.th_name=name; Input.th_entries=lst} =
  let env = List.fold_left entry empty_env lst in
    {
      Syntax.th_name = th_name;
      Syntax.th_sort = Array.of_list env.sort;
      Syntax.th_const = Array.of_list env.const;
      Syntax.th_unary = Array.of_list env.unary;
      Syntax.th_binary = Array.of_list env.binary;
      Syntax.th_predicate = Array.of_list env.predicate;
      Syntax.th_relation = Array.of_list env.relation;
      Syntax.th_equation = Array.of_list env.equation;
      Syntax.th_axiom = Array.of_list env.axiom
    }
