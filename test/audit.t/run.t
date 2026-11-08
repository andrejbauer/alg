Regression tests for the bugs found by the code audit.

A quantifier binding several variables at once. Before the fix only the
first variable was removed from the free variables of the body, so the
axiom was wrapped in vacuous outer quantifiers and evaluated n times
slower per extra variable.

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
  

An equivalence with one side still undetermined. Before the fix it
evaluated to false instead of undetermined, so the first theory had no
models and the second one too few. The alternative algorithm has its
own evaluator and gives the correct counts.

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
  

Relation entries forced under one assignment of the predicates leaked
into the enumeration of the next assignment. Before the fix the counts
were 3, 126, 43504 and depended on the order of the axioms.

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
  

An existential statement over the empty structure is false. Before the
fix the alternative algorithm took it to be true, so it found no model
of size 0 for this theory.

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
  

Axioms that contradict each other at a given size but not at smaller
ones. Before the fix the contradiction, when found while applying the
unary axioms, aborted the whole run with a fatal error instead of
yielding a count of 0.

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
  

Equations without any operation in a theory without unary operations.
Before the fix they were never checked, so every structure was passed
on as a model and the final sanity check reported an internal error.

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
  

Equations whose one side is a binary application and whose other side
mentions fewer variables. Before the fix the equation was not checked
when the last table entry it needs was filled through the side with
fewer variables, so invalid models were produced and the final sanity
check reported an internal error from size 2 on.

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
  

A relation declared twice. Before the fix the declaration was accepted,
the axioms constrained only the second copy, and the counts were
inflated by the unconstrained first copy.

  $ alg --no-source --count --size 1-3 duplicate_relation.th
  Typing error:
  R is declared more than once

A bound variable with the same name as a constant. In an equation it
was read as the constant, in any other formula as the variable, so the
two theories below had different models. Before the fix the first one
gave 1, 4, 378.

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
  

JSON output. Before the fix the commas between the tables of a model
were wrong for most signatures: a comma followed the last unary table
and the last predicate table, and none separated the last binary table
from the predicate or relation tables.

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
