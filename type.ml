type variable = string

type operation = string

type operation_index = int

type var_index = int

type arity =
  | Zero
  | One
  | Two

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
  | Var of var_index
  | Const of operation_index
  | Unary of operation_index * term
  | Binary of operation_index * term * term

type equation = term * term

(* Theory as given by the parser. *)
type raw_theory = signature * (raw_term * raw_term) list

type theory = {
  signature : signature;
  axioms : equation list
}

type algebra = {
  size : int;
  const : operation_index list;
  unary : (operation_index * int array) list;
  binary : (operation_index * int array array) list
}
