open Type

(* Return a duplicate element in the list, if one exists. *)
let rec find_duplicate = function
  | [] -> None
  | x :: xs -> if List.mem x xs then Some x else find_duplicate xs


let lookup x lst =
  try
    Some (List.assoc x lst)
  with Not_found -> None

let arity op s =
  if List.mem op s.sig_const then Some Zero
  else if List.mem op s.sig_unary then Some One
  else if List.mem op s.sig_binary then Some Two
  else None

let rec cook_term s = function
  | RawVar x ->
      begin match arity x s with
        | None -> Var x
        | Some Zero -> Const x
        | Some One | Some Two -> Error.fatal "operation %s is used as a constant" x
      end
  | RawApply (op, lst) ->
      begin match arity op s, lst with
        | None, _ -> Error.fatal "unknown operation %s" op
        | Some Zero, [] -> Const op
        | Some Zero, _ -> Error.fatal "constant %s used is used as an operation" op
        | Some One, [t] -> Unary (op, cook_term s t)
        | Some One, _ -> Error.fatal "improper use of unary operation %s" op
        | Some Two, [t1;t2] -> Binary (op, cook_term s t1, cook_term s t2)
        | Some Two, _ -> Error.fatal "improper use of binary operation %s" op
      end

let cook_axioms s a = List.map (fun (t1, t2) -> (cook_term s t1, cook_term s t2)) a
  
let cook_theory (s,a) =
  match find_duplicate (s.sig_const @ s.sig_unary @ s.sig_binary) with
    | Some op -> Error.fatal "operation %s is declared twice" op
    | None -> { signature = s; axioms = cook_axioms s a }


