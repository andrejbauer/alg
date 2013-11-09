%{
%}

%token THEORY
%token SORT
%token CONSTANT UNARY BINARY PREDICATE RELATION
%token AXIOM THEOREM
%token <string> IDENT
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token STAR PROP
%token LPAREN RPAREN
%token COLON COMMA DOT
%token FALSE TRUE
%token AND OR ARROW IMPLY IFF NOT EQUAL NOTEQUAL EXISTS FORALL
%token EOF

%left  INFIXOP0
%right INFIXOP1
%left  INFIXOP2
%left  INFIXOP3 STAR
%right INFIXOP4

%start theory
%type <Input.theory> theory

%%

theory: n = theory_name lst = list(terminated(theory_entry, DOT)) EOF
  { {Input.th_name = n; Input.th_entries = lst} }

theory_name:
  | THEORY n = IDENT DOT
    { n }

theory_entry: mark_position(plain_theory_entry) { $1 }
plain_theory_entry:
  | SORT lst = nonempty_list(sort)
    { Input.Sort lst }
  | CONSTANT lst = nonempty_list(name) COLON s = sort
    { Input.Constant (lst, s) }
  | UNARY lst = nonempty_list(name_or_prefix) COLON s1 = sort ARROW s2 = sort
    { Input.Unary (lst, (s1, s2)) }
  | BINARY lst = nonempty_list(name_or_op) COLON s1 = sort STAR s2 = sort ARROW s3 = sort
    { Input.Binary (lst, (s1, s2, s3)) }
  | PREDICATE lst = nonempty_list(name_or_prefix) COLON s = sort ARROW PROP
    { Input.Predicate (lst, s) }
  | RELATION lst = nonempty_list(name_or_op) COLON s1 = sort STAR s2 = sort ARROW PROP
    { Input.Relation (lst, (s1, s2)) }
  | AXIOM n = option(IDENT) COLON a = formula
    { Input.Axiom (n, a) }
  | THEOREM n = option(IDENT) COLON a = formula
    { Input.Axiom (n, a) }

sort:
  | x = IDENT { x }

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
  | STAR
    { "*" }
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
  | FORALL lst = nonempty_list(binder) COMMA f = formula_noquant
    { Input.Forall (lst, f) }
  | EXISTS lst = nonempty_list(binder) COMMA f = formula_noquant
    { Input.Exists (lst, f) }

(* iff_formula_noquant: mark_position(plain_iff_formula_noquant) { $1 } *)
plain_iff_formula_noquant:
  | f1 = or_formula_noquant IFF f2 = or_formula_noquant
    { Input.Iff (f1, f2) }

(* iff_formula: mark_position(plain_iff_formula) { $1 } *)
plain_iff_formula:
  | f1 = or_formula_noquant IFF f2 = or_formula
    { Input.Iff (f1, f2) }

(* imply_formula: mark_position(plain_imply_formula) { $1 } *)
plain_imply_formula:
  | f1 = or_formula_noquant IMPLY f2 = formula
    { Input.Imply (f1, f2) }
  | f1 = or_formula_noquant ARROW f2 = formula
    { Input.Imply (f1, f2) }
  | f = plain_or_formula
    { f }

or_formula: mark_position(plain_or_formula) { $1 }
plain_or_formula:
  | f1 = or_formula_noquant OR f2 = and_formula
    { Input.Or (f1, f2) }
  | f1 = or_formula_noquant OR f2 = quantified_formula
    { Input.Or (f1, f2) }
  | f = plain_and_formula
    { f }

or_formula_noquant: mark_position(plain_or_formula_noquant) { $1 }
plain_or_formula_noquant:
  | f1 = or_formula_noquant OR f2 = and_formula_noquant
    { Input.Or (f1, f2) }
  | f = plain_and_formula_noquant
    { f }

and_formula: mark_position(plain_and_formula) { $1 }
plain_and_formula:
  | f1 = and_formula_noquant AND f2 = negation_formula
    { Input.And (f1, f2) }
  | f1 = and_formula_noquant AND f2 = quantified_formula
    { Input.And (f1, f2) }
  | f = plain_negation_formula
    { f }

and_formula_noquant: mark_position(plain_and_formula_noquant) { $1 }
plain_and_formula_noquant:
  | f1 = and_formula_noquant AND f2 = negation_formula_noquant
    { Input.And (f1, f2) }
  | f = plain_negation_formula_noquant
    { f }

negation_formula: mark_position(plain_negation_formula) { $1 }
plain_negation_formula:
  | NOT f = negation_formula
    { Input.Not f }
  | NOT f = quantified_formula
    { Input.Not f }
  | f = plain_atomic_formula
    { f }

negation_formula_noquant: mark_position(plain_negation_formula_noquant) { $1 }
plain_negation_formula_noquant:
  | NOT f = negation_formula_noquant
    { Input.Not f }
  | f = plain_atomic_formula
    { f }

(* atomic_formula: mark_position(plain_atomic_formula) { $1 } *)
plain_atomic_formula:
  | TRUE
    { Input.True }
  | FALSE
    { Input.False }
  | t1 = term EQUAL t2 = term
    { Input.Equal (t1, t2) }
  | t1 = term NOTEQUAL t2 = term
    { Input.NotEqual (t1, t2) }
  | f = plain_predicate
    { f }
  | f = plain_relation
    { f }

(* predicate: mark_position(plain_predicate) { $1 } *)
plain_predicate:
  | op = PREFIXOP t = simple_term
    { Input.UnaryPr (op, t) }
  | op = name t = simple_term
    { Input.UnaryPr (op, t) }

(* relation: mark_position(plain_relation) { $1 } *)
plain_relation:
  | t1 = term op = binop t2 = term
    { Input.BinaryPr (op, t1, t2) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Input.BinaryPr (op, t1, t2) }

term: mark_position(plain_term) { $1 }
plain_term:
  | t1 = term op = binop t2 = term
    { Input.BinaryOp (op, t1, t2) }
  | op = PREFIXOP t = app_term
    { Input.UnaryOp (op, t) }
  | t = plain_app_term
    { t }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | op = name t = simple_term
    { Input.UnaryOp (op, t) }
  | op = name LPAREN t1 = term COMMA t2 = term RPAREN
    { Input.BinaryOp (op, t1, t2) }
  | t = plain_simple_term
    { t }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | x = name
    { Input.Ident x }
  | LPAREN t = plain_term RPAREN
    { t }

binder:
  | x = name
    { ([x], None) }
  | LPAREN xs = nonempty_list(name) RPAREN
    { (xs, None) }
  | LPAREN xs = nonempty_list(name) COLON s = sort RPAREN
    { (xs, Some s) }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
