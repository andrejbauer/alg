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

(* 
   Operation indices in axioms are taken from theory signature with enum_ops.
   !!!!!! This must not change, otherwise we won't get the right results. !!!!!!!
*)
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
            ; Var (List.assoc x !vars)
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

let cook_formulas s a =
  let ec = Util.enum_ops s.sig_const in
  let eu = Util.enum_ops s.sig_unary in
  let eb = Util.enum_ops s.sig_binary in
  let rec cook_term vars = function
    | RawVar x ->
      begin match arity x s with
        | None ->
          if not (List.mem_assoc x vars) then
            Error.fatal "Unquantified variable in formula."
          else
            Var (List.assoc x vars)
        | Some Zero -> Const (List.assoc x ec)
        | Some One | Some Two -> Error.fatal "operation %s is used as a constant" x
      end
    | RawApply (op, lst) ->
      begin match arity op s, lst with
        | None, _ -> Error.fatal "unknown operation %s" op
        | Some Zero, [] -> Const (List.assoc op ec)
        | Some Zero, _ -> Error.fatal "constant %s used is used as an operation" op
        | Some One, [t] -> Unary (List.assoc op eu, cook_term vars t)
        | Some One, _ -> Error.fatal "improper use of unary operation %s" op
        | Some Two, [t1;t2] -> Binary (List.assoc op eb, cook_term vars t1, cook_term vars t2)
        | Some Two, _ -> Error.fatal "improper use of binary operation %s" op
      end in
  let rec cook_formula vars = function
    | Raw_Equal (t1,t2) -> Equal (cook_term vars t1, cook_term vars t2)
    | Raw_Not_Equal (t1,t2) -> Not_Equal (cook_term vars t1, cook_term vars t2)
    | Raw_Forall (v, f) -> 
      if List.mem_assoc v vars then
        Error.fatal "Variable shadowing in formula."
      else 
        let i = List.length vars in
        Forall (i, (cook_formula ((v,i)::vars) f))
    | Raw_Exists (v, f) -> 
      if List.mem_assoc v vars then
        Error.fatal "Variable shadowing in formula."
      else 
        let i = List.length vars in
        Exists (i, (cook_formula ((v,i)::vars) f))
    | Raw_And (f1,f2) ->
      And (cook_formula vars f1, cook_formula vars f2)
    | Raw_Or (f1,f2) ->
      Or (cook_formula vars f1, cook_formula vars f2)
    | Raw_Implication (f1,f2) ->
      Implication (cook_formula vars f1, cook_formula vars f2)
    | Raw_Not f ->
      Not (cook_formula vars f) in
  List.map (cook_formula []) a

let cook_theory (s,a,r) =
  match find_duplicate (s.sig_const @ s.sig_unary @ s.sig_binary) with
    | Some op -> Error.fatal "operation %s is declared twice" op
    | None -> 
      let axioms = cook_axioms s a in
      match r with
        | None -> { signature = s; axioms = axioms; formulas=None }
        | Some lst -> 
          let restrictions = cook_formulas s lst in
          { signature = s; axioms = axioms; formulas = Some restrictions }
