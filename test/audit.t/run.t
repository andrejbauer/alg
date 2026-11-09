Regression tests for the enumeration, the front end and the output.

Posets, with the axioms quantifying several variables at once. The
counts are the numbers of posets, OEIS A000112.

  $ alg --no-source --count --size 1-5 poset_explicit.th
  # Theory poset_explicit
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 5
         4 | 16
         5 | 63
  
  Check the numbers [2, 5, 16, 63](http://oeis.org/search?q=2,5,16,63) on-line at oeis.org
  

Equivalences between relation entries, which the enumeration evaluates
while some entries are still undetermined. The default algorithm must
agree with the alternative one. At size 1 the first theory has 2 models
and the second one 6, which is easily checked by hand.

  $ alg --no-source --count --size 1-2 iff_exists.th
  # Theory iff_exists
  
      size | count
      -----|------
         1 | 2
         2 | 100
  
  $ alg --sat --no-source --count --size 1-2 iff_exists.th
  # Theory iff_exists
  
      size | count
      -----|------
         1 | 2
         2 | 100
  
  $ alg --no-source --count --size 1-2 iff_or.th
  # Theory iff_or
  
      size | count
      -----|------
         1 | 6
         2 | 1176
  
  $ alg --sat --no-source --count --size 1-2 iff_or.th
  # Theory iff_or
  
      size | count
      -----|------
         1 | 6
         2 | 1176
  

A predicate and two relations, with axioms that force relation entries
depending on the predicate. The default algorithm must agree with the
alternative one. At size 1 there are 4 models, which is easily checked
by hand.

  $ alg --no-source --count --size 1-3 leftover.th
  # Theory leftover
  
      size | count
      -----|------
         1 | 4
         2 | 136
         3 | 44224
  
  $ alg --sat --no-source --count --size 1-3 leftover.th
  # Theory leftover
  
      size | count
      -----|------
         1 | 4
         2 | 136
         3 | 44224
  

An axiom stating that there are no elements. The empty structure is its
only model, and both algorithms must find it at size 0.

  $ alg --no-source --count --size 0-2 noexists.th
  # Theory noexists
  
      size | count
      -----|------
         0 | 1
         1 | 0
         2 | 0
  
  $ alg --sat --no-source --count --size 0-2 noexists.th
  # Theory noexists
  
      size | count
      -----|------
         0 | 1
         1 | 0
         2 | 0
  

Axioms that are consistent at size 1 only, since f(x) = y forces all
elements to be equal. The larger sizes must report 0 models, and the
run must not stop at the first size without models.

  $ alg --no-source --count --size 1-3 fatal.th
  # Theory fatal
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  
  $ alg --sat --no-source --count --size 1-3 fatal.th
  # Theory fatal
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  

Equations that mention no operation, in theories without unary
operations. Both theories have models at size 1 only.

  $ alg --no-source --count --size 1-3 var_eq_const.th
  # Theory var_eq_const
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  
  $ alg --sat --no-source --count --size 1-3 var_eq_const.th
  # Theory var_eq_const
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  
  $ alg --no-source --count --size 1-3 var_eq_var.th
  # Theory var_eq_var
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  
  $ alg --sat --no-source --count --size 1-3 var_eq_var.th
  # Theory var_eq_var
  
      size | count
      -----|------
         1 | 1
         2 | 0
         3 | 0
  

Equations whose one side is an application of a binary operation and
whose other side mentions only some of its variables. The default
algorithm must agree with the alternative one.

  $ alg --no-source --count --size 1-3 gap.th
  # Theory gap
  
      size | count
      -----|------
         1 | 1
         2 | 4
         3 | 91
  
  $ alg --sat --no-source --count --size 1-3 gap.th
  # Theory gap
  
      size | count
      -----|------
         1 | 1
         2 | 4
         3 | 91
  
  $ alg --no-source --count --size 1-2 gap_two_operations.th
  # Theory gap_two_operations
  
      size | count
      -----|------
         1 | 1
         2 | 36
  
  $ alg --sat --no-source --count --size 1-2 gap_two_operations.th
  # Theory gap_two_operations
  
      size | count
      -----|------
         1 | 1
         2 | 36
  

A relation declared twice must be rejected.

  $ alg --no-source --count --size 1-3 duplicate_relation.th
  Typing error:
  R is declared more than once
  [1]

A bound variable with the same name as a constant denotes the variable,
whether the axiom is an equation or a more general formula. Both
theories say that every element is a left unit, so each has exactly
one model of every size.

  $ alg --no-source --count --size 1-3 shadow.th
  # Theory shadow
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
  
  $ alg --no-source --count --size 1-3 shadow_formula.th
  # Theory shadow_formula
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
  

JSON output for a signature with every kind of table and for one with
a single unary operation. The output must be valid JSON, in particular
the commas between the tables of a model.

  $ alg --format json --size 1 json_all.th
  [ "json_all",
    {
      "c" : 0,
      "f" : [0],
      "*" : [
        [0]
      ],
      "P" : [false],
      "R" : [
        [false]
      ]
    },
    {
      "c" : 0,
      "f" : [0],
      "*" : [
        [0]
      ],
      "P" : [false],
      "R" : [
        [true]
      ]
    },
    {
      "c" : 0,
      "f" : [0],
      "*" : [
        [0]
      ],
      "P" : [true],
      "R" : [
        [false]
      ]
    },
    {
      "c" : 0,
      "f" : [0],
      "*" : [
        [0]
      ],
      "P" : [true],
      "R" : [
        [true]
      ]
    }]
  $ alg --format json --size 1 json_unary.th
  [ "json_unary",
    {
      "f" : [0]
    }]

Default element names of a model with 18 elements. The names skip the
name of the operation, and no name may appear twice.

  $ alg --no-source --size 18 identity.th
  # Theory identity
  
  # Size 18
  
  ### identity_18_1
  
  Decomposition: identity_2_1, identity_3_1, identity_3_1
  
  
      f |  a  b  c  d  e  g  h  i  j  k  l  m  n  o  p  q  r  s
      --+------------------------------------------------------
        |  a  b  c  d  e  g  h  i  j  k  l  m  n  o  p  q  r  s
  
  
  - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  
  # Statistics
  
      size | count
      -----|------
        18 | 1
  

Asymmetric relations, with the axiom written as a negated conjunction.
The counts are the numbers of oriented graphs, OEIS A001174.

  $ alg --no-source --count --size 1-5 asymmetric.th
  # Theory asymmetric
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 7
         4 | 42
         5 | 582
  
  Check the numbers [2, 7, 42, 582](http://oeis.org/search?q=2,7,42,582) on-line at oeis.org
  

The groups of order 4. The Klein four-group is the product of two
groups of order 2, and its decomposition must be reported although
size 2 was not requested.

  $ alg --no-source --size 4 ../../theories/group.th
  # Theory group
  
  # Size 4
  
  ### group_4_1
  
  Decomposition: group_2_1, group_2_1
  
  
      inv |  1  a  b  c
      ----+------------
          |  1  a  b  c
  
  
      * |  1  a  b  c
      --+------------
      1 |  1  a  b  c
      a |  a  1  c  b
      b |  b  c  1  a
      c |  c  b  a  1
  
  
  - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  
  ### group_4_2
  
  
      inv |  1  a  b  c
      ----+------------
          |  1  a  c  b
  
  
      * |  1  a  b  c
      --+------------
      1 |  1  a  b  c
      a |  a  1  c  b
      b |  b  c  a  1
      c |  c  b  1  a
  
  
  - - - - - - - - - - - - - - - - - - - - - - - - - - - -
  
  # Statistics
  
      size | count
      -----|------
         4 | 2
  

Precedence of implication and equivalence. Equivalence binds less
tightly, so the first axiom reads (False -> True) <-> False and the
second True <-> (True -> False), which are both false, while the third
reads True <-> (forall x, x = x), which is true.

  $ alg --no-source --count --size 1 imply_iff.th
  # Theory imply_iff
  
      size | count
      -----|------
         1 | 0
  
  $ alg --no-source --count --size 1 iff_imply.th
  # Theory iff_imply
  
      size | count
      -----|------
         1 | 0
  
  $ alg --no-source --count --size 1 iff_forall.th
  # Theory iff_forall
  
      size | count
      -----|------
         1 | 1
  

A syntax error must be reported with exit status 1.

  $ alg --no-source --count --size 1 syntax_error.th
  Syntax error at line 3, characters 11-12:
  I got confused here
  [1]
