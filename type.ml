(* Singatures, terms, equations and axioms. *)

(* Variables and operations are represented as integers, but we also keep around
   the original operation names so that results can be printed. *)
type operation = int
type relation = int
type operation_name = string
type relation_name = string

type variable = int

(* A term *)
type term =
  | Var of variable
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
and formula = int array * formula'

type theory = {
  th_name : string;
  th_const : operation_name array;
  th_unary : operation_name array;
  th_binary : operation_name array;
  th_predicates : relation_name array;
  th_relations : relation_name array;
  th_equations : equation list;
  th_axioms : formula list
}

type algebra = {
  mutable alg_name : string option;
  alg_prod : string list option;
  alg_size : int;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array;
  alg_predicates : int array array;
  alg_relations : int array array array;
}

(* Used to indicate that a permanent inconsistency has been discovered. *)
exception InconsistentAxioms

(* Conversion to string, for debugging purposes. *)
let embrace s = "(" ^ s ^ ")"

let rec string_of_term = function
  | Var k -> "x" ^ string_of_int k
  | Const k -> "c" ^ string_of_int k
  | Unary (f, t) -> "u" ^ string_of_int f ^ "(" ^ string_of_term t ^ ")"
  | Binary (f, t1, t2) -> "b" ^ string_of_int f ^ "(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ ")"

let string_of_equation (t1, t2) =
  string_of_term t1 ^ " = " ^ string_of_term t2

let rec string_of_formula' = function
  | True -> "True"
  | False -> "False"
  | Predicate (r, t) -> "p" ^ string_of_int r ^ " " ^ embrace (string_of_term t)
  | Relation (r, t1, t2) -> "r" ^ string_of_int r ^ " " ^ embrace (string_of_term t1 ^ ", " ^ string_of_term t2)
  | Equal (t1, t2) -> string_of_equation (t1, t2)
  | Not f -> "not " ^ embrace (string_of_formula' f)
  | And (f1, f2) -> embrace (string_of_formula' f1) ^ " /\ " ^ embrace (string_of_formula' f2)
  | Or (f1, f2) -> embrace (string_of_formula' f1) ^ " \\/ " ^ embrace (string_of_formula' f2)
  | Imply (f1, f2) -> embrace (string_of_formula' f1) ^ " -> " ^ embrace (string_of_formula' f2)
  | Iff (f1, f2) -> embrace (string_of_formula' f1) ^ " <-> " ^ embrace (string_of_formula' f2)
  | Forall (x,f) -> "forall x" ^ string_of_int x ^ ", " ^ string_of_formula' f
  | Exists (x,f) -> "exists x" ^ string_of_int x ^ ", " ^ string_of_formula' f

let string_of_formula (a, f) = string_of_int (Array.length a) ^ " |- " ^ string_of_formula' f

let string_of_theory {th_name=name;
                      th_const=const;
                      th_unary=unary;
                      th_binary=binary;
                      th_predicates=predicates;
                      th_relations=relations;
                      th_equations=equations;
                      th_axioms=axioms} =
  "Theory: " ^ name ^ "\n" ^
  "Constant: " ^ String.concat " " (Array.to_list const) ^ "\n" ^
  "Unary: " ^ String.concat " " (Array.to_list unary) ^ "\n" ^
  "Binary: " ^ String.concat " " (Array.to_list binary) ^ "\n" ^
  "Predicates: " ^ String.concat " " (Array.to_list predicates) ^ "\n" ^
  "Relations: " ^ String.concat " " (Array.to_list relations) ^ "\n" ^
  "Equations:\n" ^ String.concat "\n" (List.map (fun (_,e) -> string_of_equation e) equations) ^ "\n" ^
  "Axioms:\n" ^ String.concat "\n" (List.map string_of_formula axioms) ^ "\n"
