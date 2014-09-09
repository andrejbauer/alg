open Theory
open Algebra


type operation = int
type relation = int
type operation_name = Input.operation
type relation_name = Input.operation

type variable = int

(* A term *)
(*type term =
  | Var of variable
  | Elem of int
  | Const of operation
  | Unary of operation * term
  | Binary of operation * term * term

(* An equation. *)
type equation' = term * term

type equation = int * equation'

(* A raw formula. *)
type formula' = 
  | True
  | False
  | Predicate of relation * term
  | Relation of relation * term * term
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
and formula = int array * formula' *)

let rec subst_term1 x t = function
  | Var y -> if x = y then Elem t else Var y
  | Elem e -> Elem e
  | Const k -> Const k
  | Unary (f, s) -> Unary (f, subst_term1 x t s)
  | Binary (f, s1, s2) -> Binary (f, subst_term1 x t s1, subst_term1 x t s2)

let rec subst_formula1 x t = function
  | True -> True
  | False -> False
  | Predicate (p, s) -> Predicate (p, subst_term1 x t s)
  | Relation (r, s1, s2) -> Relation (r, subst_term1 x t s1, subst_term1 x t s2)
  | Equal (s1, s2) -> Equal (subst_term1 x t s1, subst_term1 x t s2)
  | Not f -> Not (subst_formula1 x t f)
  | And (f1, f2) -> And (subst_formula1 x t f1, subst_formula1 x t f2)
  | Or (f1, f2) -> Or (subst_formula1 x t f1, subst_formula1 x t f2)
  | Imply (f1, f2) -> Imply (subst_formula1 x t f1, subst_formula1 x t f2)
  | Iff (f1, f2) -> Iff (subst_formula1 x t f1, subst_formula1 x t f2)
  | Forall (y, f) -> Forall (y, subst_formula1 x t f)
  | Exists (y, f) -> Exists (y, subst_formula1 x t f)

let rec compute ter algebra =
  match ter with
    | Var x -> x
    | Elem x -> x
    | Const x -> x
    | Unary (x, ter1) -> algebra.alg_unary.(x).(compute ter1 algebra)
    | Binary (x, ter1, ter2) -> algebra.alg_binary.(x).(compute ter1 algebra).(compute ter2 algebra)

let rec does_contradict axiom algebra =
  let chck_forall var form algebra =
    let rec ch_forall var form algebra varvalue =
      match does_contradict (subst_formula1 var varvalue form) algebra with
        | false -> if varvalue + 1 < algebra.alg_size then ch_forall var form algebra (varvalue + 1) else false
        | true -> true
    in
    ch_forall var form algebra 0
  in
  let chck_exists var form algebra =
    let rec ch_exists var form algebra varvalue =
      match does_contradict (subst_formula1 var varvalue form) algebra with
        | false -> false
        | true -> if varvalue + 1 < algebra.alg_size then ch_exists var form algebra (varvalue + 1) else true
    in
    ch_exists var form algebra 0
  in
  let rec chck axiom = 
    match axiom with
      | True -> false
      | False -> true
      | Predicate (rel, ter) -> false (*???*)
      | Relation (rel, ter1, ter2) -> false (*???*)
      | Equal (ter1, ter2) -> 
        compute ter1 <> compute ter2
      | Forall (var, form) -> 
        chck_forall var form algebra
      | Exists (var, form) ->
        chck_exists var form algebra
      | And (form1, form2) ->
        does_contradict form1 algebra || does_contradict form2 algebra
      | Or (form1, form2) -> 
        does_contradict form1 algebra && does_contradict form2 algebra
      | Imply (form1, form2) ->
        let result = does_contradict form1 algebra in
        if not result then false else not (does_contradict form2 algebra) (*result <> does_contradict form2 algebra*)
      | Iff (form1, form2) ->
        does_contradict form1 algebra <> does_contradict form2 algebra
      | Not form -> not (does_contradict form algebra)
  in
  chck axiom

      
    
    
    
    
    