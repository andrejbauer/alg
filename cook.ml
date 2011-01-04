(* A simple compiler from abstract syntax to the internal representation. *)

module S = Syntax
module T = Type

type env = {
  const : (S.operation * T.operation) list ;
  unary : (S.operation * T.operation) list ;
  binary : (S.operation * T.operation) list ;
  predicates : (S.operation * T.relation) list ;
  relations : (S.operation * T.relation) list ;
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

let lookup_const {const=ec} x = Util.lookup x ec

let lookup_unary {unary=eu} x = Util.lookup x eu

let lookup_binary {binary=eb} x = Util.lookup x eb

let lookup_predicate {predicates=ep} x = Util.lookup x ep

let lookup_relation {relations=er} x = Util.lookup x er

let lookup_var vars x = Util.lookup x vars

let is_op {const=ec; unary=eu; binary=eb} x =
  List.mem_assoc x ec || List.mem_assoc x eu || List.mem_assoc x eb

(* The free variables of a term, without repetitions. *)
let rec fv_term env = function
  | S.Var x ->
      if is_op env x then [] else [x]
  | S.Apply (_, lst) ->
      List.fold_left (fun xs t -> Util.union (fv_term env t) xs) [] lst
  | _ -> Error.fatal "malformed term encountered by fv_term"

(* The free variables of a formula, without repetitions. *)
let rec fv_formula env = function
  | S.False -> []
  | S.True -> []
  | S.Apply (_, lst) -> List.fold_left (fun xs t -> Util.union (fv_term env t) xs) [] lst
  | S.Equal (t1, t2) -> Util.union (fv_term env t1) (fv_term env t2)
  | S.Not f -> fv_formula env f
  | S.And (f1, f2) | S.Or (f1, f2) | S.Imply (f1, f2) | S.Iff (f1, f2) ->
      Util.union (fv_formula env f1) (fv_formula env f2)
  | S.Forall (x, f) | S.Exists (x, f) ->
      Util.remove x (fv_formula env f)
  | _ -> Error.fatal "malformed formula encountered by fv_formula"

(* The depth of the formula is the maximum level of nesting of quantifiers. *)
let rec depth = function
  | S.Var _ -> Error.fatal "malformed formula encountered by depth"
  | S.False -> 0
  | S.True -> 0
  | S.Apply _ -> 0
  | S.Equal _ -> 0
  | S.Not f -> depth f
  | S.And (f1, f2) | S.Or (f1, f2) | S.Imply (f1, f2) | S.Iff (f1, f2) -> max (depth f1) (depth f2)
  | S.Forall (_, f) | S.Exists (_, f) -> 1 + depth f

let rec cook_term env vars = function
  | S.Var x ->
      begin match lookup_var vars x with
        | Some k -> T.Var k
        | None ->
            begin match lookup_const env x with
              | Some k -> T.Const k
              | None ->
                  if is_op env x then
                    Error.fatal "operation %s is used as a constant" x
                  else
                    Error.fatal "unknown variable %s" x
            end
      end
  | S.Apply (op, lst) ->
      begin match lookup_const env op, lst with
        | Some c, [] -> T.Const c
        | Some c, _::_ -> Error.fatal "constant %s is used as an operation" op
        | None, _ ->
            begin match lookup_unary env op, lst with
              | Some u, [t] -> T.Unary (u, cook_term env vars t)
              | Some u, lst -> Error.fatal "unary operation %s applied to %d arguments" op (List.length lst)
              | None, _ ->
                  begin match lookup_binary env op, lst with
                    | Some b, [t1; t2] -> T.Binary (b, cook_term env vars t1, cook_term env vars t2)
                    | Some b, lst -> Error.fatal "binary operation %s applied to %d arguments" op (List.length lst)
                    | None, _ -> Error.fatal "unknown operation %s" op
                  end
            end
      end
  | _ -> Error.fatal "malformed term encountered by cook_term"

let cook_equation env (t1, t2) =
  let k, vars = Util.enum (Util.union (fv_term env t1) (fv_term env t2)) in
    (k, (cook_term env vars t1, cook_term env vars t2))

let cook_formula env f =
  let rec cook vars = function
    | S.Var _ -> Error.fatal "malformed formula ecountered by cook_formula"
    | S.True -> T.True
    | S.False -> T.False
    | S.Apply (op, lst) ->
        begin match lookup_predicate env op, lst with
          | Some u, [t] -> T.Predicate (u, cook_term env vars t)
          | Some u, lst -> Error.fatal "predicate %s applied to %d arguments" op (List.length lst)
          | None, _ ->
              begin match lookup_relation env op, lst with
                | Some b, [t1; t2] -> T.Relation (b, cook_term env vars t1, cook_term env vars t2)
                | Some b, lst -> Error.fatal "relation %s applied to %d arguments" op (List.length lst)
                | None, _ -> Error.fatal "unknown predicate or relation %s" op
              end
        end
    | S.Equal (t1, t2) -> T.Equal (cook_term env vars t1, cook_term env vars t2)
    | S.And (f1,f2) -> T.And (cook vars f1, cook vars f2)
    | S.Or (f1,f2) -> T.Or (cook vars f1, cook vars f2)
    | S.Imply (f1,f2) -> T.Imply (cook vars f1, cook vars f2)
    | S.Iff (f1,f2) -> T.Iff (cook vars f1, cook vars f2)
    | S.Not f -> T.Not (cook vars f)
    | S.Forall (x, f) ->
        let vars, k = extend_var x vars in
          T.Forall (k, cook vars f)
    | S.Exists (x, f) -> 
        let vars, k = extend_var x vars in
          T.Exists (k, cook vars f)
  in
  let f = List.fold_right (fun x g -> S.Forall (x, g)) (fv_formula env f) f in
    Array.make (depth f) (-1), cook [] f

let split_entries lst =
  List.fold_left
    (fun (env,eqs,axs) -> function
       | S.Constant cs -> (List.fold_left extend_const env cs, eqs, axs)
       | S.Unary us -> (List.fold_left extend_unary env us, eqs, axs)
       | S.Binary bs -> (List.fold_left extend_binary env bs, eqs, axs)
       | S.Predicate ps -> (List.fold_left extend_predicate env ps, eqs, axs)
       | S.Relation rs -> (List.fold_left extend_relation env rs, eqs, axs)
       | S.Axiom (_,a) ->
           begin match S.as_equation a with
             | None -> (env, eqs, a :: axs)
             | Some (t1,t2) -> (env, (t1,t2) :: eqs, axs)
           end)
    (empty_env, [], [])
    lst

let env_to_array lst =
  let a = Array.make (List.length lst) "?" in
    List.iter (fun (op,k) -> a.(k) <- op) lst ;
    a

let cook_theory th_name lst =
  let (env, eqs, axs) = split_entries lst in
    match Util.find_duplicate (List.map fst (env.const @ env.unary @ env.binary)) with
      | Some op -> Error.fatal "operation %s is declared more than once" op
      | None -> 
          {
            T.th_name = th_name;
            T.th_const = env_to_array env.const;
            T.th_unary = env_to_array env.unary;
            T.th_binary = env_to_array env.binary;
            T.th_predicates = env_to_array env.predicates;
            T.th_relations = env_to_array env.relations;
            T.th_equations = List.map (cook_equation env) eqs;
            T.th_axioms = List.map (cook_formula env) axs;
          }
