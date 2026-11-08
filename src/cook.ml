(* A simple compiler from abstract syntax to the internal representation. *)

type env = {
  const : (Theory.operation_name * Theory.operation) list ;
  unary : (Theory.operation_name * Theory.operation) list ;
  binary : (Theory.operation_name * Theory.operation) list ;
  predicates : (Theory.relation_name * Theory.relation) list ;
  relations : (Theory.relation_name * Theory.relation) list ;
}

let empty_env = { const = []; unary = []; binary = []; predicates = []; relations = []}

let fresh lst = 1 + List.fold_left (fun m (_,k) -> max m k) (-1) lst

let extend_const env c = 
  { env with const = (c, fresh env.const) :: env.const }

let extend_unary env u = 
  { env with unary = (u, fresh env.unary) :: env.unary }

let extend_binary env b = 
  { env with binary = (b, fresh env.binary) :: env.binary }

let extend_predicate env p = 
  { env with predicates = (p, fresh env.predicates) :: env.predicates }

let extend_relation env r = 
  { env with relations = (r, fresh env.relations) :: env.relations }

let extend_var x vars =
  let k = fresh vars in
    (x,k) :: vars, k

let lookup_const {const=ec; _} x = Util.lookup x ec

let lookup_unary {unary=eu; _} x = Util.lookup x eu

let lookup_binary {binary=eb; _} x = Util.lookup x eb

let lookup_predicate {predicates=ep; _} x = Util.lookup x ep

let lookup_relation {relations=er; _} x = Util.lookup x er

let lookup_var vars x = Util.lookup x vars

let is_op {const=ec; unary=eu; binary=eb; _} x =
  List.mem_assoc x ec || List.mem_assoc x eu || List.mem_assoc x eb

(* The free variables of a term, without repetitions. A name in [bound] is a
   variable even when it is also declared as a constant or an operation. *)
let rec fv_term env bound (t, _) =
  match t with
    | Input.Var x ->
      if is_op env x && not (List.mem x bound) then [] else [x]
    | Input.UnaryOp (_, t) -> fv_term env bound t
    | Input.BinaryOp (_, t1, t2) -> Util.union (fv_term env bound t1) (fv_term env bound t2)


(* The free variables of a formula, without repetitions. *)
let rec fv_formula env bound (f, _) =
  match f with
    | Input.False -> []
    | Input.True -> []
    | Input.Equal (t1, t2)
    | Input.NotEqual (t1, t2) ->
      Util.union (fv_term env bound t1) (fv_term env bound t2)
    | Input.UnaryPr (_, t) -> fv_term env bound t
    | Input.BinaryPr (_, t1, t2) -> Util.union (fv_term env bound t1) (fv_term env bound t2)
    | Input.Not f -> fv_formula env bound f
    | Input.And (f1, f2)
    | Input.Or (f1, f2)
    | Input.Imply (f1, f2)
    | Input.Iff (f1, f2) ->
      Util.union (fv_formula env bound f1) (fv_formula env bound f2)
    | Input.Forall (xs, f) | Input.Exists (xs, f) ->
      Util.remove_many xs (fv_formula env (xs @ bound) f)

(* The depth of the formula is the maximum level of nesting of quantifiers. *)
let rec depth (f, _) =
  match f with
    | Input.False
    | Input.True
    | Input.UnaryPr _
    | Input.BinaryPr _
    | Input.Equal _
    | Input.NotEqual _ -> 0
    | Input.Not f -> depth f
    | Input.And (f1, f2)
    | Input.Or (f1, f2)
    | Input.Imply (f1, f2)
    | Input.Iff (f1, f2) -> max (depth f1) (depth f2)
    | Input.Forall (xs, f) | Input.Exists (xs, f) -> List.length xs + depth f
      
let rec cook_term env vars (t,loc) =
  match t with
  | Input.Var x ->
      begin match lookup_var vars x with
        | Some k -> Theory.Var k
        | None ->
            begin match lookup_const env x with
              | Some k -> Theory.Const k
              | None -> Error.typing_error ~loc "unknown variable or constant %s" x
            end
      end
  | Input.UnaryOp (op, t) ->
    begin match lookup_unary env op with
      | Some u -> Theory.Unary (u, cook_term env vars t)
      | None -> Error.typing_error ~loc "%s is used as a unary operation but it is not" op
    end
  | Input.BinaryOp (op, t1, t2) ->
    begin match lookup_binary env op with
      | Some b -> Theory.Binary (b, cook_term env vars t1, cook_term env vars t2)
      | None -> Error.typing_error ~loc "%s is used as a unary operation but it is not" op
    end

let cook_equation env (xs, t1, t2) =
  let k, vars = Util.enum (Util.union (fv_term env xs t1) (fv_term env xs t2)) in
    (k, (cook_term env vars t1, cook_term env vars t2))

let cook_formula env f =
  let rec cook vars (f,loc) =
    match f with
      | Input.True -> Theory.True
      | Input.False -> Theory.False
      | Input.UnaryPr (op, t) ->
        begin match lookup_predicate env op with
          | Some u -> Theory.Predicate (u, cook_term env vars t)
          | None -> Error.typing_error ~loc "%s is not a unary predicate" op
        end
      | Input.BinaryPr (op, t1, t2) ->
        begin match lookup_relation env op with
          | Some b -> Theory.Relation (b, cook_term env vars t1, cook_term env vars t2)
          | None -> Error.typing_error ~loc "%s is not a binary relation" op
        end
      | Input.Equal (t1, t2) -> Theory.Equal (cook_term env vars t1, cook_term env vars t2)
      | Input.NotEqual (t1, t2) ->
        Theory.Not (Theory.Equal (cook_term env vars t1, cook_term env vars t2))
      | Input.And (f1,f2) -> Theory.And (cook vars f1, cook vars f2)
      | Input.Or (f1,f2) -> Theory.Or (cook vars f1, cook vars f2)
      | Input.Imply (f1,f2) -> Theory.Imply (cook vars f1, cook vars f2)
      | Input.Iff (f1,f2) -> Theory.Iff (cook vars f1, cook vars f2)
      | Input.Not f -> Theory.Not (cook vars f)
      | Input.Forall (xs, f) ->
        begin match xs with
          | [] -> cook vars f
          | x :: xs ->
            let vars, k = extend_var x vars in
              Theory.Forall (k, cook vars (Input.Forall (xs, f), loc))
        end
      | Input.Exists (xs, f) ->
        begin match xs with
          | [] -> cook vars f
          | x :: xs ->
            let vars, k = extend_var x vars in
              Theory.Exists (k, cook vars (Input.Exists (xs, f), loc))
        end
  in
  let loc = snd f in
  let xs = fv_formula env [] f in
  let f = Input.Forall (xs, f), loc in
    Array.make (depth f) (-1), cook [] f

let split_entries lst =
  List.fold_left
    (fun (env,eqs,axs) ->
      fun (e, _) -> match e with
        | Input.Constant cs -> (List.fold_left extend_const env cs, eqs, axs)
        | Input.Unary us -> (List.fold_left extend_unary env us, eqs, axs)
        | Input.Binary bs -> (List.fold_left extend_binary env bs, eqs, axs)
        | Input.Predicate ps -> (List.fold_left extend_predicate env ps, eqs, axs)
        | Input.Relation rs -> (List.fold_left extend_relation env rs, eqs, axs)
        | Input.Axiom (_,a) ->
          begin match Input.as_equation a with
            | None -> (env, eqs, a :: axs)
            | Some (xs, t1, t2) -> (env, (xs, t1, t2) :: eqs, axs)
          end)
    (empty_env, [], [])
    lst

let env_to_array lst =
  let a = Array.make (List.length lst) "?" in
    List.iter (fun (op,k) -> a.(k) <- op) lst ;
    a

let cook_theory th_name lst =
  let (env, eqs, axs) = split_entries lst in
    match Util.find_duplicate (List.map fst (env.const @ env.unary @ env.binary @ env.predicates @ env.relations)) with
      | Some op -> Error.typing_error ~loc:Common.Nowhere "%s is declared more than once" op
      | None -> 
          {
            Theory.th_name = th_name;
            Theory.th_const = env_to_array env.const;
            Theory.th_unary = env_to_array env.unary;
            Theory.th_binary = env_to_array env.binary;
            Theory.th_predicates = env_to_array env.predicates;
            Theory.th_relations = env_to_array env.relations;
            Theory.th_equations = List.map (cook_equation env) eqs;
            Theory.th_axioms = List.map (cook_formula env) axs;
          }
