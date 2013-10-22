(* Abstract syntax as produced by the parser. *)

type variable = string
type operation = string

type term = term' * Common.position
and term' =
  | Var of variable
  | UnaryOp of operation * term
  | BinaryOp of operation * term * term

type formula = formula' * Common.position
and formula' =
  | True
  | False
  | Equal of term * term
  | Predicate of operation * term
  | Relation of operation * term * term
  | Forall of variable * formula
  | Exists of variable * formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula
  | Not of formula

type theory_entry = theory_entry' * Common.position
and theory_entry' =
  | Constant of operation list
  | Unary of operation list
  | Binary of operation list
  | Predicate of operation list
  | Relation of operation list
  | Axiom of string option * formula

type theory_name = string

type theory = { th_name : theory_name option ; th_entries : theory_entry list }

(* [as_equation f] tries to convert an axiom to an equation. *)
let rec as_equation (f, _) =
  match f with
    | Equal (t1, t2) -> Some (t1, t2)
    | Forall (_, f) -> as_equation f
    | False | True | Predicate _ | Relation _ | 
        Exists _ | And _ | Or _ | Imply _ | Iff _ | Not _ -> None
