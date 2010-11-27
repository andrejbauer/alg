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

type raw_formula =
  | Raw_Equal of raw_term * raw_term
  | Raw_Not_Equal of raw_term * raw_term
  | Raw_Forall of variable * raw_formula
  | Raw_Exists of variable * raw_formula
  | Raw_And of raw_formula * raw_formula
  | Raw_Or of raw_formula * raw_formula
  | Raw_Implication of raw_formula * raw_formula
  | Raw_Not of raw_formula

type formula = 
  | Equal of term * term
  | Not_Equal of term * term
  | Forall of var_index * formula
  | Exists of var_index * formula
  | And of formula * formula
  | Or of formula * formula
  | Implication of formula * formula
  | Not of formula

(* Theory as given by the parser. *)
type raw_theory = signature * (raw_term * raw_term) list * raw_formula list option

type theory = {
  signature : signature;
  axioms : equation list;
  formulas : formula list option
}

type algebra = {
  size : int;
  const : operation_index list;
  unary : (operation_index * int array) list;
  binary : (operation_index * int array array) list
}
