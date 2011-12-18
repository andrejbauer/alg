(* Abstract syntax as produced by the parser. *)

type variable = string
type operation = string

type expr =
  | Var of variable
  | Apply of operation * term list
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

and term = expr

and formula = expr

type theory_entry =
  | Constant of operation list
  | Unary of operation list
  | Binary of operation list
  | Predicate of operation list
  | Relation of operation list
  | Axiom of string option * formula

type theory_name = string

type theory = theory_name option * theory_entry list

(* [as_equation f] tries to convert an axiom to an equation. *)
let rec as_equation = function
  | False | True | Apply _ | Var _ | Exists _ | And _ | Or _ | Imply _ | Iff _ | Not _ -> None
  | Equal (t1, t2) -> Some (t1, t2)
  | Forall (_, f) -> as_equation f
