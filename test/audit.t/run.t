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
  
