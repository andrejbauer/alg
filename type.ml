type variable = string

type operation = string

type signature = {
  sig_const : operation list;
  sig_unary: operation list;
  sig_binary: operation list
}

(* This is what the parser gives. *)
type raw_term =
  | RawVar of variable
  | RawApply of operation * raw_term list

type term =
  | Var of string
  | Const of operation
  | Unary of operation * term
  | Binary of operation * term * term

type equation = term * term

(* Theory as given by the parser. *)
type raw_theory = signature * (raw_term * raw_term) list

type theory = {
  signature : signature;
  axioms : equation list
}

type structure = {
  size : int;
  const : (operation * int) list;
  unary : (operation * int array) list;
  binary : (operation * int array array) list
}
