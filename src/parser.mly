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
%type <Input.theory> theory

%%

theory: n = option(theory_name) lst = list(terminated(theory_entry, DOT)) EOF
  { {Input.th_name = n; Input.th_entries = lst} }

theory_name:
  | THEORY n = IDENT DOT
    { n }

theory_entry: mark_position(_theory_entry) { $1 }
_theory_entry:
  | CONSTANT lst = nonempty_list(name)
    { Input.Constant lst }
  | UNARY lst = nonempty_list(name_or_prefix)
    { Input.Unary lst }
  | BINARY lst = nonempty_list(name_or_op)
    { Input.Binary lst }
  | PREDICATE lst = nonempty_list(name_or_prefix)
    { Input.Predicate lst }
  | RELATION lst = nonempty_list(name_or_op)
    { Input.Relation lst }
  | AXIOM n = option(IDENT) COLON a = formula
    { Input.Axiom (n, a) }
  | THEOREM n = option(IDENT) COLON a = formula
    { Input.Axiom (n, a) }

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

formula: mark_position(_formula) { $1 }
_formula:
  | f = _quantified_formula
    { f }
  | f = _iff_formula
    { f }
  | f = _imply_formula
    { f }

formula_noquant: mark_position(_formula_noquant) { $1 }
_formula_noquant:
  | f = _quantified_formula
    { f }
  | f = _imply_formula
    { f }
  | f = _iff_formula_noquant
    { f }

quantified_formula: mark_position(_quantified_formula) { $1 }
_quantified_formula:
  | FORALL xs = vars COMMA f = formula_noquant
    { Input.Forall (xs, f) }
  | EXISTS xs = vars COMMA f = formula_noquant
    { Input.Exists (xs, f) }

(* iff_formula_noquant: mark_position(_iff_formula_noquant) { $1 } *)
_iff_formula_noquant:
  | f1 = or_formula_noquant IFF f2 = or_formula_noquant
    { Input.Iff (f1, f2) }

(* iff_formula: mark_position(_iff_formula) { $1 } *)
_iff_formula:
  | f1 = or_formula_noquant IFF f2 = or_formula
    { Input.Iff (f1, f2) }

(* imply_formula: mark_position(_imply_formula) { $1 } *)
_imply_formula:
  | f1 = or_formula_noquant IMPLY f2 = formula
    { Input.Imply (f1, f2) }
  | f = _or_formula
    { f }

or_formula: mark_position(_or_formula) { $1 }
_or_formula:
  | f1 = or_formula_noquant OR f2 = and_formula
    { Input.Or (f1, f2) }
  | f1 = or_formula_noquant OR f2 = quantified_formula
    { Input.Or (f1, f2) }
  | f = _and_formula
    { f }

or_formula_noquant: mark_position(_or_formula_noquant) { $1 }
_or_formula_noquant:
  | f1 = or_formula_noquant OR f2 = and_formula_noquant
    { Input.Or (f1, f2) }
  | f = _and_formula_noquant
    { f }

and_formula: mark_position(_and_formula) { $1 }
_and_formula:
  | f1 = and_formula_noquant AND f2 = negation_formula
    { Input.And (f1, f2) }
  | f1 = and_formula_noquant AND f2 = quantified_formula
    { Input.And (f1, f2) }
  | f = _negation_formula
    { f }

and_formula_noquant: mark_position(_and_formula_noquant) { $1 }
_and_formula_noquant:
  | f1 = and_formula_noquant AND f2 = negation_formula_noquant
    { Input.And (f1, f2) }
  | f = _negation_formula_noquant
    { f }

negation_formula: mark_position(_negation_formula) { $1 }
_negation_formula:
  | NOT f = negation_formula
    { Input.Not f }
  | NOT f = quantified_formula
    { Input.Not f }
  | f = _atomic_formula
    { f }

negation_formula_noquant: mark_position(_negation_formula_noquant) { $1 }
_negation_formula_noquant:
  | NOT f = negation_formula_noquant
    { Input.Not f }
  | f = _atomic_formula
    { f }

(* atomic_formula: mark_position(_atomic_formula) { $1 } *)
_atomic_formula:
  | TRUE
    { Input.True }
  | FALSE
    { Input.False }
  | t1 = term EQUAL t2 = term
    { Input.Equal (t1, t2) }
  | t1 = term NOTEQUAL t2 = term
    { Input.NotEqual (t1, t2) }
  | f = _predicate
    { f }
  | f = _relation
    { f }

(* predicate: mark_position(_predicate) { $1 } *)
_predicate:
  | op = PREFIXOP t = simple_term
    { Input.UnaryPr (op, t) }
  | op = name t = simple_term
    { Input.UnaryPr (op, t) }

(* relation: mark_position(_relation) { $1 } *)
_relation:
  | t1 = term op = binop t2 = term
    { Input.BinaryPr (op, t1, t2) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Input.BinaryPr (op, t1, t2) }

term: mark_position(_term) { $1 }
_term:
  | t1 = term op = binop t2 = term
    { Input.BinaryOp (op, t1, t2) }
  | op = PREFIXOP t = app_term
    { Input.UnaryOp (op, t) }
  | t = _app_term
    { t }

app_term: mark_position(_app_term) { $1 }
_app_term:
  | op = name t = simple_term
    { Input.UnaryOp (op, t) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Input.BinaryOp (op, t1, t2) }
  | t = _simple_term
    { t }

simple_term: mark_position(_simple_term) { $1 }
_simple_term:
  | x = name
    { Input.Var x }
  | LPAREN t = _term RPAREN
    { t }

vars:
  | vs = nonempty_list(name)
    { vs }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
