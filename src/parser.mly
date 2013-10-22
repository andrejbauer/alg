%{
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

theory_entry: mark_position(plain_theory_entry) { $1 }
plain_theory_entry:
  | CONSTANT lst = nonempty_list(name)
    { Syntax.Constant lst }
  | UNARY lst = nonempty_list(name_or_prefix)
    { Syntax.Unary lst }
  | BINARY lst = nonempty_list(name_or_op)
    { Syntax.Binary lst }
  | PREDICATE lst = nonempty_list(name_or_prefix)
    { Syntax.Predicate lst }
  | RELATION lst = nonempty_list(name_or_op)
    { Syntax.Relation lst }
  | AXIOM n = option(IDENT) COLON a = expr
    { Syntax.Axiom (n, a) }
  | THEOREM n = option(IDENT) COLON a = expr
    { Syntax.Axiom (n, a) }

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

formula: mark_position(plain_formula) { $1 }
plain_formula:
  | f = plain_quantified_formula
    { f }
  | f = plain_iff_formula
    { f }
  | f = plain_imply_formula
    { f }

formula_noquant: mark_position(plain_formula_noquant) { $1 }
plain_formula_noquant:
  | f = plain_quantified_formula
    { f }
  | f = plain_imply_formula
    { f }
  | f = plain_iff_formula_noquant
    { f }

quantified_formula: mark_position(plain_quantified_formula) { $1 }
plain_quantified_formula:
  | FORALL xs = vars COMMA f = formula_noquant
    { List.fold_right (fun x f -> Syntax.Forall (x, f)) xs f }
  | EXISTS xs = vars COMMA f = formula_noquant
    { List.fold_right (fun x f -> Syntax.Exists (x, f)) xs f }

iff_formula_noquant: mark_position(plain_iff_formula_noquant) { $1 }
plain_iff_formula_noquant:
  | f1 = or_formula_noquant IFF f2 = or_formula_noquant
    { Syntax.Iff (f1, f2) }

iff_formula: mark_position(plain_iff_formula) { $1 }
plain_iff_formula:
  | f1 = or_formula_noquant IFF f2 = or_formula
    { Syntax.Iff (f1, f2) }

imply_formula: mark_position(plain_imply_formula) { $1 }
plain_imply_formula:
  | f1 = or_formula_noquant IMPLY f2 = formula
    { Syntax.Imply (f1, f2) }
  | f = plain_or_formula
    { f }

or_formula: mark_position(plain_or_formula) { $1 }
plain_or_formula:
  | f1 = or_formula_noquant OR f2 = and_formula
    { Syntax.Or (f1, f2) }
  | f1 = or_formula_noquant OR f2 = quantified_formula
    { Syntax.Or (f1, f2) }
  | f = and_formula
    { f }

or_formula_noquant: mark_position(plain_or_formula_noquant) { $1 }
plain_or_formula_noquant:
  | f1 = or_formula_noquant OR f2 = and_formula_noquant
    { Syntax.Or (f1, f2) }
  | f = plain_and_formula_noquant
    { f }

and_formula: mark_position(plain_and_formula) { $1 }
plain_and_formula:
  | f1 = and_formula_noquant AND f2 = negation_formula
    { Syntax.And (f1, f2) }
  | f1 = and_formula_noquant AND f2 = quantified_formula
    { Syntax.And (f1, f2) }
  | f = plain_negation_formula
    { f }

and_formula_noquant: mark_position(plain_and_formula_noquant) { $1 }
plain_and_formula_noquant:
  | f1 = and_formula_noquant AND f2 = negation_formula_noquant
    { Syntax.And (f1, f2) }
  | f = negation_formula_noquant
    { f }

negation_formula: mark_position(plain_negation_formula) { $1 }
plain_negation_formula:
  | NOT f = negation_formula
    { Syntax.Not f }
  | NOT f = quantified_formula
    { Syntax.Not f }
  | f = plain_atomic_formula
    { f }

negation_formula_noquant: mark_position(plain_negation_formula_noquant) { $1 }
plain_negation_formula_noquant:
  | NOT f = negation_formula_noquant
    { Syntax.Not f }
  | f = plain_atomic_formula
    { f }

atomic_formula: mark_position(plain_atomic_formula) { $1 }
plain_atomic_formula:
  | TRUE
    { Syntax.True }
  | FALSE
    { Syntax.False }
  | t1 = term EQUAL t2 = term
    { Syntax.Equal (t1, t2) }
  | t1 = term NOTEQUAL t2 = term
    { Syntax.Not (Syntax.Equal (t1, t2)) }
  | f = plain_predicate
    { f }
  | f = plain_relation
    { f }

predicate: mark_position(plain_predicate) { $1 }
plain_predicate:
  | op = PREFIXOP t = simple_term
    { Syntax.Predicate (op, t) }
  | op = name t = simple_term
    { Syntax.Predicate (op, t) }

relation:
  | t1 = term op = binop t2 = term
    { Syntax.Relation (op, t1, t2) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Syntax.Relation (op, t1, t2) }

term: mark_position(plain_term) { $1 }
plain_term:
  | t1 = term op = binop t2 = term
    { Syntax.BinaryOp (op, t1, t2) }
  | op = PREFIXOP t = app_term
    { Syntax.UnaryOp (op, t) }
  | t = app_term
    { t }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | op = name t = simple_term
    { Syntax.UnaryOp (op, t) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Syntax.BinaryOp (op, t1, t2) }
  | t = plain_simple_term
    { t }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | x = name
    { Syntax.Var x }
  | LPAREN t = plain_term RPAREN
    { t }

vars:
  | vs = nonempty_list(name)
    { vs }

%%
