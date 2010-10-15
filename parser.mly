%{
  open Type
%}

%token ZERO ONE TWO
%token SIGNATURE AXIOMS
%token <string> IDENT
%token LPAREN RPAREN
%token SEMICOLON COLON COMMA EQUAL
%token EOF

%start theory
%type <Type.raw_theory> theory

%%

theory: s = signature a = axioms EOF
  { (s,a) }

signature: SIGNATURE COLON lst = list(op_declaration)
  { List.fold_left (fun s -> function
                      | (0, op) -> {s with sig_const = op :: s.sig_const}
                      | (1, op) -> {s with sig_unary = op :: s.sig_unary}
                      | (2, op) -> {s with sig_binary = op :: s.sig_binary}
                      | _ -> assert false)
      { sig_const = []; sig_unary = []; sig_binary = [] } lst
  }

axioms: AXIOMS COLON lst = list(terminated(equation, SEMICOLON))
  { lst }

name:
  | ZERO      { "0" }
  | ONE       { "1" }
  | TWO       { "2" }
  | x = IDENT { x }

op_declaration: op = name COLON k = arity
  { (k, op) }

arity:
  | ZERO { 0 }
  | ONE  { 1 }
  | TWO  { 2 }

equation: t1 = term EQUAL t2 = term
  { (t1, t2) }

term:
  | x = name
    { RawVar x }
  | op = name LPAREN lst = args RPAREN
    { RawApply (op, lst) }
  | LPAREN t = term RPAREN
    { t }

args:
  | 
    { [] }
  | t = term
    { [t] }
  | t = term COMMA ts = args
    { t :: ts }

%%
