(* Singatures, terms, equations and axioms. *)

(* Variables and operations are represented as integers, but we also keep around
   the original operation names so that results can be printed. *)
type operation = int
type operation_name = string
type variable = int

(* A term *)
type term =
  | Var of variable
  | Const of operation
  | Unary of operation * term
  | Binary of operation * term * term

(* An equation. *)
type equation = term * term

(* A raw formula. *)
type formula' = 
  | True
  | False
  | Equal of term * term
  | Forall of variable * formula'
  | Exists of variable * formula'
  | And of formula' * formula'
  | Or of formula' * formula'
  | Imply of formula' * formula'
  | Iff of formula' * formula'
  | Not of formula'

(* A formula in a context. The context is an array which is large enough for evaluation
   of the formula. *)
and formula = int array * formula'

type theory = {
  th_const : operation_name array;
  th_unary : operation_name array;
  th_binary : operation_name array;
  th_equations : equation list;
  th_axioms : formula list
}

type algebra = {
  alg_size : int;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array
}
