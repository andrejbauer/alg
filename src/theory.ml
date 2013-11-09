open Syntax

(* Used to indicate that a permanent inconsistency has been discovered. *)
exception InconsistentAxioms

(* Substitution functions. *)
let rec subst_term x t = function
  | Var y -> if x = y then t else Var y
  | Elem e -> Elem e
  | Const k -> Const k
  | Unary (f, s) -> Unary (f, subst_term x t s)
  | Binary (f, s1, s2) -> Binary (f, subst_term x t s1, subst_term x t s2)

let rec subst_formula x t = function
  | True -> True
  | False -> False
  | Predicate (p, s) -> Predicate (p, subst_term x t s)
  | Relation (r, s1, s2) -> Relation (r, subst_term x t s1, subst_term x t s2)
  | Equal (s1, s2) -> Equal (subst_term x t s1, subst_term x t s2)
  | Not f -> Not (subst_formula x t f)
  | And (f1, f2) -> And (subst_formula x t f1, subst_formula x t f2)
  | Or (f1, f2) -> Or (subst_formula x t f1, subst_formula x t f2)
  | Imply (f1, f2) -> Imply (subst_formula x t f1, subst_formula x t f2)
  | Iff (f1, f2) -> Iff (subst_formula x t f1, subst_formula x t f2)
  | Forall (y, s, f) ->
    if x = y then Forall (y, s, f) else Forall (y, s, subst_formula x t f)
  | Exists (y, s, f) ->
    if x = y then Forall (y, s, f) else Exists (y, s, subst_formula x t f)
