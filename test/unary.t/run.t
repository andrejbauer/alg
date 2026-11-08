Equations with a unary operation under a binary one. Before the fix for
issue 17 alg reported 2675 and 10470 models of size 3.

  $ alg --no-source --count --size 1-3 free_under_unary.th
  # Theory free_under_unary
  
      size | count
      -----|------
         1 | 1
         2 | 20
         3 | 1849
  

  $ alg --no-source --count --size 1-3 star.th
  # Theory star
  
      size | count
      -----|------
         1 | 1
         2 | 12
         3 | 3642
  
