%{
  open Type
%}

%token ZERO ONE TWO
%token SIGNATURE AXIOMS RESTRICTIONS EXISTS FORALL
%token <string> IDENT
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token LPAREN RPAREN
%token SEMICOLON COLON COMMA DOT EQUAL 
%token EOF

%token AND OR IMPLICATION NOT NOTEQUAL 

%right IMPLICATION
%nonassoc NOTEQUAL
%left EQUAL

%left OR
%left AND
%left NOT

%left  INFIXOP0
%right INFIXOP1
%left  INFIXOP2
%left  INFIXOP3
%right INFIXOP4

%start theory
%type <Type.raw_theory> theory

%%

theory: s = signature a = axioms r = option(restriction) EOF
  { (s,a,r) }

signature: SIGNATURE COLON lst = list(op_declaration)
  { List.fold_left (fun s -> function
                      | (Zero, op) -> {s with sig_const = op :: s.sig_const}
                      | (One, op) -> {s with sig_unary = op :: s.sig_unary}
                      | (Two, op) -> {s with sig_binary = op :: s.sig_binary})
      { sig_const = []; sig_unary = []; sig_binary = [] } lst
  }

axioms: AXIOMS COLON lst = list(terminated(equation, SEMICOLON))
  { lst }

restriction: RESTRICTIONS COLON lst = list(terminated(formula, DOT))
    { lst }

formula: 
  | f = simple_formula
    { f }
  | l = formula op = logical_connective r = formula
    { op (l,r) }
  | NOT f = formula
    { Raw_Not f }
  | FORALL x = name COLON f = formula 
    { Raw_Forall (x,f) }
  | EXISTS x = name COLON f = formula 
    { Raw_Exists (x,f) }

simple_formula:
  | t1 = term EQUAL t2 = term
    { Raw_Equal (t1,t2) }
  | t1 = term NOTEQUAL t2 = term
    { Raw_Not_Equal (t1,t2) }
  | LPAREN f = formula RPAREN
    { f }

%inline logical_connective:
  | AND           { fun (a,b) -> Raw_And (a,b) }
  | OR            { fun (a,b) -> Raw_Or (a,b) }
  | IMPLICATION   { fun (a,b) -> Raw_Implication (a,b)}

name:
  | ZERO      { "0" }
  | ONE       { "1" }
  | TWO       { "2" }
  | x = IDENT { x }

name_or_op:
  | n = name
    { n }
  | op = binop
    { op }
  | op = PREFIXOP
    { op }

op_declaration: op = name_or_op COLON k = arity
  { (k, op) }

arity:
  | ZERO { Zero }
  | ONE  { One }
  | TWO  { Two }

equation: t1 = term EQUAL t2 = term
  { (t1, t2) }

term:
  | t1 = term op = binop t2 = term
    { RawApply(op, [t1;t2]) }
  | op = PREFIXOP t = simple_term
    { RawApply(op, [t]) }
  | t = simple_term
    { t}

simple_term:
  | x = name
    { RawVar x }
  | op = name LPAREN lst = args RPAREN
    { RawApply (op, lst) }
  | LPAREN t = term RPAREN
    { t }

%inline binop: 
  | op = INFIXOP0
    { op }
  | op = INFIXOP1
    { op }
  | op = INFIXOP2
    { op }
  | op = INFIXOP3
    { op }
  | op = INFIXOP4
    { op }

args:
  | 
    { [] }
  | t = term
    { [t] }
  | t = term COMMA ts = args
    { t :: ts }

%%
