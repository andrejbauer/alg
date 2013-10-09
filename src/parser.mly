%{
  open Syntax
%}

%token THEORY
%token CONSTANT UNARY BINARY PREDICATE RELATION
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
  | PREDICATE lst = nonempty_list(name_or_prefix)
    { Predicate lst }
  | RELATION lst = nonempty_list(name_or_op)
    { Relation lst }
  | AXIOM n = option(IDENT) COLON a = expr
    { Axiom (n, a) }
  | THEOREM n = option(IDENT) COLON a = expr
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

expr:
  | f = quantified_expr
  | f = iff_expr
  | f = imply_expr
    { f }

expr_noquant:
  | f = quantified_expr
  | f = imply_expr
  | f = iff_expr_noquant
    { f }

quantified_expr:
  | FORALL xs = vars COMMA f = expr_noquant
    { List.fold_right (fun x f -> Forall (x, f)) xs f }
  | EXISTS xs = vars COMMA f = expr_noquant
    { List.fold_right (fun x f -> Exists (x, f)) xs f }

iff_expr_noquant:
  | f1 = or_expr_noquant IFF f2 = or_expr_noquant
    { Iff (f1, f2) }

iff_expr:
  | f1 = or_expr_noquant IFF f2 = or_expr
    { Iff (f1, f2) }

imply_expr:
  | f1 = or_expr_noquant IMPLY f2 = expr
    { Imply (f1, f2) }
  | f = or_expr
    { f }

or_expr:
  | f1 = or_expr_noquant OR f2 = and_expr
    { Or (f1, f2) }
  | f1 = or_expr_noquant OR f2 = quantified_expr
    { Or (f1, f2) }
  | f = and_expr
    { f }

or_expr_noquant:
  | f1 = or_expr_noquant OR f2 = and_expr_noquant
    { Or (f1, f2) }
  | f = and_expr_noquant
    { f }

and_expr:
  | f1 = and_expr_noquant AND f2 = negation_expr
  | f1 = and_expr_noquant AND f2 = quantified_expr
    { And (f1, f2) }
  | f = negation_expr
    { f }

and_expr_noquant:
  | f1 = and_expr_noquant AND f2 = negation_expr_noquant
    { And (f1, f2) }
  | f = negation_expr_noquant
    { f }

negation_expr:
  | NOT f = negation_expr
  | NOT f = quantified_expr
    { Not f }
  | f = atomic_expr
    { f }

negation_expr_noquant:
  | NOT f = negation_expr_noquant
    { Not f }
  | f = atomic_expr
    { f }

atomic_expr:
  | t = term
     { t }
  | t1 = term EQUAL t2 = term
    { Equal (t1, t2) }
  | t1 = term NOTEQUAL t2 = term
    { Not (Equal (t1, t2)) }
  | TRUE
    { True }
  | FALSE
    { False }

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
  | LPAREN t = expr RPAREN
    { t }

vars:
  | vs = nonempty_list(name)
    { vs }

%%
