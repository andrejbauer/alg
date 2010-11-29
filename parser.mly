%{
  open Syntax
%}

%token CONSTANT UNARY BINARY
%token EQUATION AXIOM
%token <string> IDENT
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token LPAREN RPAREN
%token COLON COMMA DOT
%token FALSE TRUE
%token AND OR IMPLY IFF NOT EQUAL NOTEQUAL EXISTS FORALL
%token EOF

%nonassoc IFF
%right IMPLY
%left OR
%left AND
%nonassoc NOT
%left  INFIXOP0
%right INFIXOP1
%left  INFIXOP2
%left  INFIXOP3
%right INFIXOP4

%start theory
%type <Syntax.theory> theory

%%

theory: t = list(terminated(theory_entry, DOT)) EOF
  { t }

theory_entry:
  | CONSTANT lst = nonempty_list(name)
    { Constant lst }
  | UNARY lst = nonempty_list(name_or_prefix)
    { Unary lst }
  | BINARY lst = nonempty_list(name_or_op)
    { Binary lst }
  | EQUATION n = statement_name e = equation
    { Equation (n, e) }
  | AXIOM n = statement_name a = formula
    { Axiom (n, a) }

name:
  | x = IDENT { x }

statement_name:
  | n = option (terminated (IDENT, COLON))
    { n }

name_or_prefix:
  | n = name
    { n }
  | op = PREFIXOP
    { op }

name_or_op:
  | n = name
    { n }
  | op = binop
    { op }

equation: t1 = term EQUAL t2 = term
  { (t1, t2) }

term:
  | t1 = term op = binop t2 = term
    { Apply(op, [t1;t2]) }
  | op = PREFIXOP t = simple_term
    { Apply(op, [t]) }
  | t = simple_term
    { t}

simple_term:
  | x = name
    { Var x }
  | op = name LPAREN lst = args RPAREN
    { Apply (op, lst) }
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

formula:
  | FORALL xs = vars COMMA f = formula
    { List.fold_right (fun x f -> Forall (x, f)) xs f }
  | EXISTS xs = vars COMMA f = formula
    { List.fold_right (fun x f -> Exists (x, f)) xs f }
  | f = simple_formula
    { f }

vars:
  | vs = nonempty_list(name)
    { vs }

simple_formula:
  | f1 = simple_formula c = connective f2 = simple_formula
    { c f1 f2 }
  | NOT f = simple_formula
    { Not f }
  | f = atomic_formula
    { f }

atomic_formula:
  | t1 = term EQUAL t2 = term
    { Equal (t1, t2) }
  | t1 = term NOTEQUAL t2 = term
    { Not (Equal (t1, t2)) }
  | TRUE
    { True }
  | FALSE
    { False }
  | LPAREN f = formula RPAREN
    { f }

%inline connective:
  | AND     { fun a b -> And (a,b) }
  | OR      { fun a b -> Or (a,b) }
  | IMPLY   { fun a b -> Imply (a,b)}
  | IFF     { fun a b -> Iff (a,b)}

%%
