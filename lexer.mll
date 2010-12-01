{ 
  open Lexing
  open Parser
}

let ident = ['_' 'a'-'z' 'A'-'Z' '0'-'9']+ '\''*

let symbolchar = ['!' '$' '%' '&' '*' '+' '-' '/' '\\' ':' '<' '=' '>' '?' '@' '^' '|' '~']
let prefixop = ['?' '!'] symbolchar* | '~'  symbolchar+
let infixop0 = ['|' '&' '$']  symbolchar*
let infixop1 = ['@' '^']      symbolchar*
let infixop2 = ['+' '-' '\\'] symbolchar*
let infixop4 = "**"           symbolchar*
let infixop3 = ['*' '/' '%']  symbolchar*

rule token = parse
  | '#' [^'\n']* '\n'   { new_line lexbuf; token lexbuf }
  | '\n'                { new_line lexbuf; token lexbuf }
  | [' ' '\t']          { token lexbuf }
  | "Theory"            { THEORY }
  | "Constants"         { CONSTANT }
  | "Constant"          { CONSTANT }
  | "Unary"             { UNARY }
  | "Binary"            { BINARY }
  | "Equation"          { EQUATION }
  | "Axiom"             { AXIOM }
  | "forall"            { FORALL }
  | "exists"            { EXISTS }
  | "True"              { TRUE }
  | "False"             { FALSE }
  | "/\\"               { AND }
  | "\\/"               { OR }
  | "->"                { IMPLY }
  | "<->"               { IFF }
  | "=>"                { IMPLY }
  | "<=>"               { IFF }
  | "<>"                { NOTEQUAL }
  | "!="                { NOTEQUAL }
  | "~"                 { NOT }
  | "not"               { NOT }
  | "."                 { DOT }

  | ident               { IDENT (lexeme lexbuf) }
  | prefixop            { PREFIXOP (Lexing.lexeme lexbuf) }
  | infixop0            { INFIXOP0 (Lexing.lexeme lexbuf) }
  | infixop1            { INFIXOP1 (Lexing.lexeme lexbuf) }
  | infixop2            { INFIXOP2 (Lexing.lexeme lexbuf) }
  | infixop4            (* Comes before infixop3 because ** matches the infixop3 pattern too *)
                        { INFIXOP4 (Lexing.lexeme lexbuf) }
  | infixop3            { INFIXOP3 (Lexing.lexeme lexbuf) }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | ':'                 { COLON }
  | ','                 { COMMA }
  | '='                 { EQUAL }
  | eof                 { EOF }

{
}
