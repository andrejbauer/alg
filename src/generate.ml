(* The backgracking mechanism. *)

(* At any moment alg has the following:

   1. A stateful partially built model.
   2. A priority queue of conditions that need to be satisfied.

   Progress is made by taking an action (filling in a table entry)
   that helps satisfy a condition. When this is done, other conditions
   are affected, so their priority can change.

   Alg does the following:

   * take the first condition off the queue

   * generate actions that lead towards satisfying the condition

   * for each generated action, perform the action, reprocess the
     affected conditions in the queue (including the first one),
     and call the whole thing recursively.
*)

(* A term. *)
type term =
  | Elem of element
  | Const of const
  | Unary of unary * term
  | Binary of binary * term * term

(* A boolean formula. *)
type formula =
  | False
  | True
  | Equal of Syntax.sort * term * term
  | Unequal of Syntax.sort * term * term
  | Predicate of Syntax.index * term
  | Relation of Syntax.index * term * term
  | And of formula list
  | Or of formula list

(* Priority computes the branching factor of a formula, i.e.,
   how many times we will restart the continuation when processing
   the formula. *)

(* Upper estimate on the size of the range of a term. *)
let range alg size = function
  | Const k ->  
    let const = {Syntax.th_unary} = alg in
    let _, s = const.(k) in size.(s) (* XXX can be improved *)
  | Elem _ -> 1
  | Unary (op, _) -> 
    let unary = {Syntax.th_unary} = alg in
    let _, (_, s) = unary.(op) in size.(s)
  | Binary (op, _, _) ->
    let binary = {Syntax.th_binary} = alg in
    let _, (_, _, s) = binary.(op) in size.(s)

(* If we try to equate the term with a value, how much
   branching are we going to perform (upper bound, best estimate)? *)
let term_priority alg size =
  let {Syntax.th_unary=unary; Syntax.th_binary=binary} = alg in
  let rec priority = function
    | Const k -> k + 1
    | Elem _
    | Unary (_, Elem _)
    | Binary (_, Elem _, Elem _) -> 1
    | Unary (op, t) ->
      let _, (s, _) = unary.(op) in
        size.(s) * priority t
    | Binary (op, t1, t2) ->
      let _, (s1, s2, _) = binary.(op) in
        size.(s1) * size.(s2) * priority t1 * priority t2
  in
    priority

let formula_priority alg size = function
  | False -> 0
  | True -> 1
  | Equal (t, Elem _, _)
  | Equal (Elem _, t, _) ->
    term_priority alg size t
  | Equal (t1, t2, s) ->
    size.(s) * term_priority alg size t1 * term_priority alg size t2
  | Unequal (Const k, Elem _, s) ->
  | Unequal (t, Elem _, s)
  | Unequal (Elem _, t, s) ->
    (size.(s) - 1) * term_priority alg size t

type condition = int * formula

type conditions = condition list

module Q = Queue.Make(
  struct
    type t = condition

    let compare (p1, f1) (p2, f2) =
      if p1 < p2 then Util.Less
      else if p1 > p2 then Util.Greater
      else let c = Pervasives.compare f1 f2 with
        if c < 0 then Util.less
        else if c > 0 then Util.Greater
        else Equal
  end)

(* The current state of generation process. It should be possible
   to checkpoint the generation process by storing one of these.
*)
type state = {
  st_theory : Syntax.theory ; (* The theory we're generating *)
  st_model : Algebra.algebra ; (* The partially built model, stateful *)
  st_queue : queue ; (* The priority queue of conditions to be satisfied, persistent *)
  st_const : conditions array ; (* conditions affected by filling in a constant *)
  st_unary : conditions array aray ; (* conditions affected by filling in a unary entry  *)
  st_binary : conditions array aray array ; (* conditions affected by filling in a binary entry *)
  st_predicate : conditions array array ; (* conditions affected by filling in a predicate entry *)
  st_relation : conditions array aray array ; (* conditions affected by filling in a relation entry *)
}

let add_dependents ((p, f) as c) =
  let rec add_term state = function
    | Elem _ -> state
    | Const k -> state.st_const.(k) <- c :: state.st_const.(k)
    | Unary (op, Elem k) -> state.st_unary.(op).(k) <- c :: state.st_unary.(op).(k)
    | Binary (op, Elem k1, Elem k2) -> state.st_binary.(op).(k1).(k2) <- c :: state.st_binary.(op).(k1).(k2)
    | Unary (_, t) -> add_term state t
    | Binary (_, t1, t2) -> add_state 
  in
  let rec add_formula state = function
    | False -> state
    | True -> state
    | Equal (t1, t2)
    | Unequal (t1, t2)
    | Relation (_, t1, t2) ->
      add_term (add_term state t1) t2
    | Predicate (_, t) -> add_term state t
    | And lst
    | Or lst -> List.fold_left add_formula state lst
  in
    add_formula f

let rec force_or k state lst = function
  | [] -> ()
  | f :: fs ->

and force_predicate k state p i b =
    
and force_formula state f b k =
  let {Algebra.alg_size=size;
       Algebra.alg_predicate=predicate} = state.st_model
  in
  match b, f with
  | false, False -> k state
  | true, False -> ()
  | false, True -> ()
  | true, True -> k state

  | true, Equal (s, t1, t2)
  | false, Unequal (s, t1, t2) ->

  | false, Equal (s, t1, t2)
  | true, Unequal (s, t1, t2) -> 


  | b, Predicate (p, t) ->
    let v = eval_term alg t in
      
    begin match eval_term alg t with

    | Elem i -> force_predicate state p i b k
    | t ->
      let (_, s) = predicate.(p) in
      let n = size.(s) in
        for i = 0 to n - 1 do
          force_term state t i
            (fun state -> force_predicate state p i b k)
        done ;
    end

  | b, Relation (r, t1, t2) ->
    
  | true, And lst -> 
    k (List.fold_left (fun state f -> enqueue_formula state f true) lst)
  | false, Or lst ->
    k (List.fold_left (fun state f -> enqueue_formula state f false) lst)
  | false, Or lst -> force_


let rec generate k state =
  match Q.dequeue state.st_queue with
   | None -> k state.st_model
   | Some (f, b), queue -> force_formula (generate k) { state with st_queue = queue } b f


