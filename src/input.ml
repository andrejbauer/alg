(* Abstract syntax as produced by the parser. *)

type ident = string

type var = ident
type sort = ident
type const = ident
type unary = ident
type binary = ident
type predicate = ident
type relation = ident

type term = term' * Common.position
and term' =
  | Ident of var
  | UnaryOp of unary * term
  | BinaryOp of binary * term * term

type formula = formula' * Common.position
and formula' =
  | True
  | False
  | Equal of term * term
  | NotEqual of term * term
  | UnaryPr of predicate * term
  | BinaryPr of relation * term * term
  | Forall of (var list * sort option) list * formula
  | Exists of (var list * sort option) list * formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula
  | Not of formula

type theory_entry = theory_entry' * Common.position
and theory_entry' =
  | Sort of sort list
  | Constant of const list * sort
  | Unary of unary list * (sort * sort)
  | Binary of binary list * (sort * sort * sort)
  | Predicate of predicate list * sort
  | Relation of relation list * (sort * sort)
  | Axiom of string option * formula

type theory = { th_name : string ; th_entries : theory_entry list }
