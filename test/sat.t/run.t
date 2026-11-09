Theories whose axioms are negated equations: functions without fixed
points and binary operations without idempotent elements. The default
and the alternative algorithm must give the same counts.

  $ alg --no-source --count --size 1-5 fixedpointfree.th
  # Theory fixedpointfree
  
      size | count
      -----|------
         1 | 0
         2 | 1
         3 | 2
         4 | 6
         5 | 13
  
  Check the numbers [1, 2, 6, 13](http://oeis.org/search?q=1,2,6,13) on-line at oeis.org
  

  $ alg --sat --no-source --count --size 1-5 fixedpointfree.th
  # Theory fixedpointfree
  
      size | count
      -----|------
         1 | 0
         2 | 1
         3 | 2
         4 | 6
         5 | 13
  
  Check the numbers [1, 2, 6, 13](http://oeis.org/search?q=1,2,6,13) on-line at oeis.org
  

  $ alg --no-source --count --size 1-3 nonidempotent.th
  # Theory nonidempotent
  
      size | count
      -----|------
         1 | 0
         2 | 3
         3 | 978
  

  $ alg --sat --no-source --count --size 1-3 nonidempotent.th
  # Theory nonidempotent
  
      size | count
      -----|------
         1 | 0
         2 | 3
         3 | 978
  
