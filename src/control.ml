(* We attempt to describe abstractly the backtracking
   mechanism used by alg. *)

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

let search state conditions compute_actions cont =
  match dequeue conditions with
    | None ->
      (* All conditions have been satisfied, pass the solution to the continuation *)
      cont state
    | Some c ->
      let actions = compute_actions state c in
        List.iter
          (fun (act, unact) -> )
          (compute_actions state c)
