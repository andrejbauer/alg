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


let cook_axioms s a =
  let ec = Util.enum_ops s.sig_const in
  let eu = Util.enum_ops s.sig_unary in
  let eb = Util.enum_ops s.sig_binary in
  let cook_axiom (left, right) =
    (* This is for enumerating variables inside an axiom for faster access. *)
    let vars = ref [] in 
    let rec cook_term = function
      | RawVar x ->
        begin match arity x s with
          | None ->
            if not (List.mem_assoc x !vars) then
              vars := (x, List.length !vars) :: !vars
            else () ; Var (List.assoc x !vars)
          | Some Zero -> Const (List.assoc x ec)
          | Some One | Some Two -> Error.fatal "operation %s is used as a constant" x
        end
      | RawApply (op, lst) ->
        begin match arity op s, lst with
          | None, _ -> Error.fatal "unknown operation %s" op
          | Some Zero, [] -> Const (List.assoc op ec)
          | Some Zero, _ -> Error.fatal "constant %s used is used as an operation" op
          | Some One, [t] -> Unary (List.assoc op eu, cook_term t)
          | Some One, _ -> Error.fatal "improper use of unary operation %s" op
          | Some Two, [t1;t2] -> Binary (List.assoc op eb, cook_term t1, cook_term t2)
          | Some Two, _ -> Error.fatal "improper use of binary operation %s" op
        end in
    (cook_term left, cook_term right) in
  List.map cook_axiom a

let cook_theory (s,a) =
  match find_duplicate (s.sig_const @ s.sig_unary @ s.sig_binary) with
    | Some op -> Error.fatal "operation %s is declared twice" op
    | None -> { signature = s; axioms = cook_axioms s a }
