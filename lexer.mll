{ 
  open Lexing
  open Parser
}

let ident = ['_' 'a'-'z' 'A'-'Z' '0'-'9']* '\''*

let symbolchar = ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']
let prefixop = ['~' '?' '!']             symbolchar*
let infixop0 = ['=' '<' '>' '|' '&' '$'] symbolchar*
let infixop1 = ['@' '^']                 symbolchar*
let infixop2 = ['+' '-']                 symbolchar*
let infixop4 = "**"                      symbolchar*
let infixop3 = ['*' '/' '%']             symbolchar*

rule token = parse
  | '#' [^'\n']* '\n'   { new_line lexbuf; token lexbuf }
  | '\n'                { new_line lexbuf; token lexbuf }
  | [' ' '\t']          { token lexbuf }
  | '0'                 { ZERO }
  | '1'                 { ONE }
  | '2'                 { TWO }
  | "signature"         { SIGNATURE }
  | "axioms"            { AXIOMS }
  | ident               { IDENT (lexeme lexbuf) }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | ':'                 { COLON }
  | ';'                 { SEMICOLON }
  | ','                 { COMMA }
  | '='                 { EQUAL }
  | eof                 { EOF }

{
}
