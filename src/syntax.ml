(** Internal syntax. *)

(* Variables and operations are indexed by integers. *)
type index = int

type var = index
type sort = index
type const = index
type unary = index
type binary = index
type predicate = index
type relation = index

(* Elements of structure are integers. *)
type element = int

(* A term *)
type term =
  | Var of var
  | Elem of element
  | Const of const
  | Unary of unary * term
  | Binary of binary * term * term

(* NB: we assume that each quantifier abstracts a different variable,
   and that the variables appearing in a formula are numbered from 0 to n-1 *)

(* An equation with information about the types of variables. *)
type equation_ctx = {
  eq_var : sort array ;
  eq_lhs : term ;
  eq_rhs : term
}

(* A formula *)
type formula = 
  | True
  | False
  | Predicate of predicate * term
  | Relation of relation * term * term
  | Equal of term * term
  | Forall of var * sort * formula
  | Exists of var * sort * formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula
  | Not of formula

type theory = {
  th_name : string;
  th_sort : Input.sort array;
  th_const : (Input.const * int * sort) array; (* the int is the max value a constant may take *)
  th_unary : (Input.unary * (sort * sort)) array;
  th_binary : (Input.binary * (sort * sort * sort)) array;
  th_predicate : (Input.predicate * sort) array;
  th_relation : (Input.relation * (sort * sort)) array;
  th_equation : equation_ctx list;
  th_axiom : (element array * formula) list (* NB: all formulas must be closed *)
}
