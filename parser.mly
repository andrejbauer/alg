%{
  open Syntax
%}

%token THEORY
%token CONSTANT UNARY BINARY
%token AXIOM THEOREM
%token <string> IDENT
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token LPAREN RPAREN
%token COLON COMMA DOT
%token FALSE TRUE
%token AND OR IMPLY IFF NOT EQUAL NOTEQUAL EXISTS FORALL
%token EOF

%left  INFIXOP0
%right INFIXOP1
%left  INFIXOP2
%left  INFIXOP3
%right INFIXOP4

%start theory
%type <Syntax.theory> theory

%%

theory: n = option(theory_name) t = list(terminated(theory_entry, DOT)) EOF
  { (n, t) }

theory_name:
  | THEORY n = IDENT DOT
    { n }

theory_entry:
  | CONSTANT lst = nonempty_list(name)
    { Constant lst }
  | UNARY lst = nonempty_list(name_or_prefix)
    { Unary lst }
  | BINARY lst = nonempty_list(name_or_op)
    { Binary lst }
  | AXIOM n = option(IDENT) COLON a = formula
    { Axiom (n, a) }
  | THEOREM n = option(IDENT) COLON a = formula
    { Axiom (n, a) }

name:
  | x = IDENT { x }

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

term:
  | t1 = term op = binop t2 = term
    { Apply (op, [t1;t2]) }
  | op = PREFIXOP t = simple_term
    { Apply (op, [t]) }
  | t = simple_term
    { t }

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
  | f = quantified_formula
  | f = iff_formula
  | f = imply_formula
    { f }

formula_noquant:
  | f = quantified_formula
  | f = imply_formula
  | f = iff_formula_noquant
    { f }

quantified_formula:
  | FORALL xs = vars COMMA f = formula_noquant
    { List.fold_right (fun x f -> Forall (x, f)) xs f }
  | EXISTS xs = vars COMMA f = formula_noquant
    { List.fold_right (fun x f -> Exists (x, f)) xs f }

iff_formula_noquant:
  | f1 = or_formula_noquant IFF f2 = or_formula_noquant
    { Iff (f1, f2) }

iff_formula:
  | f1 = or_formula_noquant IFF f2 = or_formula
    { Iff (f1, f2) }

imply_formula:
  | f1 = or_formula_noquant IMPLY f2 = formula
    { Imply (f1, f2) }
  | f = or_formula
    { f }

or_formula:
  | f1 = or_formula_noquant OR f2 = and_formula
    { Or (f1, f2) }
  | f1 = or_formula_noquant OR f2 = quantified_formula
    { Or (f1, f2) }
  | f = and_formula
    { f }

or_formula_noquant:
  | f1 = or_formula_noquant OR f2 = and_formula_noquant
    { Or (f1, f2) }
  | f = and_formula_noquant
    { f }

and_formula:
  | f1 = and_formula_noquant AND f2 = negation_formula
  | f1 = and_formula_noquant AND f2 = quantified_formula
    { And (f1, f2) }
  | f = negation_formula
    { f }

and_formula_noquant:
  | f1 = and_formula_noquant AND f2 = negation_formula_noquant
    { And (f1, f2) }
  | f = negation_formula_noquant
    { f }

negation_formula:
  | NOT f = negation_formula
  | NOT f = quantified_formula
    { Not f }
  | f = atomic_formula
    { f }

negation_formula_noquant:
  | NOT f = negation_formula_noquant
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

vars:
  | vs = nonempty_list(name)
    { vs }

%%
