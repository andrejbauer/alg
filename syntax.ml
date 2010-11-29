(* Abstract syntax as produced by the parser. *)

type variable = string
type operation = string

type term =
  | Var of variable
  | Apply of operation * term list

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

type theory_entry =
  | Constant of operation list
  | Unary of operation list
  | Binary of operation list
  | Equation of string option * equation
  | Axiom of string option * formula

type theory = theory_entry list

(* [as_equation f] tries to convert an axiom to an equation. *)
let rec as_equation = function
  | False | True | Exists _ | And _ | Or _ | Imply _ | Iff _ | Not _ -> None
  | Equal (t1, t2) -> Some (t1, t2)
  | Forall (_, f) -> as_equation f
