(* Definitions common to many files. *)

(** Position in source code. For each type in the abstract syntax we define two versions
    [t] and [t']. The former is the latter with a position tag. For example, [expr = expr'
    * position] and [expr'] is the type of expressions (without positions). 
*)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown position *)

(** [nowhere e] is the expression [e] without a source position. It is used when
    an expression is generated and there is not reasonable position that could be
    assigned to it. *)
let nowhere x = (x, Nowhere)

(** Convert a position as presented by [Lexing] to [position]. *)
let position_of_lex lex =
  Position (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)

