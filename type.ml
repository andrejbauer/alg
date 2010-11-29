(* Singatures, terms, equations and axioms. *)

(* Variables and operations are represented as integers, but we also keep around
   the original operation names so that results can be printed. *)
type operation = int
type operation_name = string
type variable = int

type term =
  | Var of variable
  | Const of operation
  | Unary of operation * term
  | Binary of operation * term * term

type equation = term * term

type formula = 
  | True
  | False
  | Equal of term * term
  | Forall of variable * formula
  | Exists of variable * formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula
  | Not of formula

type theory = {
  th_const : (operation * operation_name) list;
  th_unary : (operation * operation_name) list;
  th_binary : (operation * operation_name) list;
  th_equations : equation list;
  th_axioms : formula list
}

type algebra = {
  alg_size : int;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array
}
