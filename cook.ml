(* A simple compiler from abstract syntax to the internal representation. *)

module S = Syntax
module T = Type

type env = {
  const : (S.operation * T.operation) list ;
  unary : (S.operation * T.operation) list ;
  binary : (S.operation * T.operation) list ;
  vars : (S.variable * T.variable) list
}

let empty_env = { const = []; unary = []; binary = []; vars = [] }

let fresh lst = 1 + List.fold_left (fun m (_,k) -> max m k) (-1) lst

let extend_const c env = 
  { env with const = (c, fresh env.const) :: env.const }

let extend_unary u env = 
  { env with unary = (u, fresh env.unary) :: env.unary }

let extend_binary b env = 
  { env with binary = (b, fresh env.binary) :: env.binary }

let extend_var x env =
  let k = fresh env.vars in
    { env with vars = (x,k) :: env.vars }, k

let lookup_const {const=ec} x = Util.lookup x ec

let lookup_unary {unary=eu} x = Util.lookup x eu

let lookup_binary {binary=eb} x = Util.lookup x eb

let lookup_var {vars=ev} x = Util.lookup x ev

let cook_term env t =
  let rec cook env = function
    | S.Var x ->
        begin match lookup_const env x with
          | Some c -> env, T.Const c
          | None ->
              if List.mem_assoc x env.unary || List.mem_assoc x env.binary then
                Error.fatal "operation %s is used as a constant" x
              else
                begin match lookup_var env x with
                  | Some i -> env, T.Var i
                  | None ->
                      let env, k = extend_var x env in
                        env, T.Var k
                end
        end
      | S.Apply (op, lst) ->
          begin match lookup_const env op, lst with
            | Some c, [] -> env, T.Const c
            | Some c, _::_ -> Error.fatal "constant %s is used as an operation" op
            | None, _ ->
                begin match lookup_unary env op, lst with
                  | Some u, [t] ->
                      let env, t = cook env t in
                        env, T.Unary (u, t)
                  | Some u, lst ->
                      Error.fatal "unary operation %s applied to %d arguments" op (List.length lst)
                  | None, _ ->
                      begin match lookup_binary env op, lst with
                        | Some b, [t1; t2] ->
                            let env, t1 = cook env t1 in
                            let env, t2 = cook env t2 in
                              env, T.Binary (b, t1, t2)
                        | Some b, lst ->
                            Error.fatal "binary operation %s applied to %d arguments" op (List.length lst)
                        | None, _ ->
                            Error.fatal "unknown operation %s" op
                      end
                end
          end
 in
  cook env t

let cook_equation env (t1, t2) =
  let env, t1 = cook_term env t1 in
  let env, t2 = cook_term env t2 in
    env, (t1, t2)

let cook_axiom env a =
  let rec cook env = function
    | S.True -> env, T.True
    | S.False -> env, T.False
    | S.Equal (t1, t2) -> 
        let env, t1 = cook_term env t1 in
        let env, t2 = cook_term env t2 in
          env, Equal (t1, t2)
    | S.Forall (x, f) -> 
        let env, k = extend_var x env in
        let env, f = cook env f in
          List.remove_assoc x env, S.Forall (k, f)
    | S.Exists (x, f) -> 
        let env, k = extend_var x env in
        let env, f = cook env f in
          List.remove_assoc x env, S.Exists (k, f)
    | S.And (f1,f2) ->
        let env, f1 = cook env f1 in
        let env, f2 = cook env f2 in
          env, And (f1, f2)
    | S.Or (f1,f2) ->
        let env, f1 = cook env f1 in
        let env, f2 = cook env f2 in
          env, Or (f1, f2)
    | S.Imply (f1,f2) ->
        let env, f1 = cook env f1 in
        let env, f2 = cook env f2 in
          env, Imply (f1, f2)
    | S.Iff (f1,f2) ->
        let env, f1 = cook env f1 in
        let env, f2 = cook env f2 in
          env, Iff (f1, f2)
    | S.Not f ->
        let env, f = cook env f in
          env, Not f
  in
    cook env a

let rec collect_env lst =
  List.fold_left
    (fun env -> function
       | Constant c -> extend_const c env
       | Unary u -> extend_unary u env
       | Binary b -> extend_binary b env
       | Equation _ | Axiom _ -> env)
    empty_env
    lst

let collect_equations lst =
  Util.filter_map
    (function
       | Equation (t1,t2) -> Some (t1,t2)
       | Axiom a -> S.as_equation a
       | _ -> None)
    lst

let collect_axioms lst =
  Util.filter_map
    (function
       | Axiom a ->
           begin match S.as_equation a with
             | None -> Some a
             | Some _ -> None
           end
       |_ -> None)
    lst

let cook_theory lst =
  let env = collect_env lst in
    match find_duplicate (List.map fst (env.const @ env.unary @ env.binary)) with
      | Some op -> Error.fatal "operation %s is declared more than once" op
      | None -> 
          let env, eqs =
            List.fold_left
              (fun (env,eqs) eq -> let env, eq = cook_equation env eq in (env, eq::eqs))
              (collect_equations lst)
          in
          let env, axs =
            List.fold_left
              (fun (env,axs) ax -> let env, ax = cook_axiom env ax in (env, ax::axs))
              (collect_axioms lst)
          in
            {
              th_const = Util.invert env.const;
              th_unary = Util.invert env.unary;
              th_binary = Util.invert env.binary;
              th_equations = eqs;
              th_axioms = axs;
            }
