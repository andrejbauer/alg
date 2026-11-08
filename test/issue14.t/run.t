Parenthesized formulas, issue 14. None of these theories parsed before the fix.

  $ alg --no-source --count --size 1-3 quantifier.th
  # Theory quantifier
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
  

  $ alg --no-source --count --size 1-4 ../../theories/graph.th
  # Theory Graph
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 4
         4 | 11
  
  Check the numbers [2, 4, 11](http://oeis.org/search?q=2,4,11) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/digraph.th
  # Theory Directed_Graph
  
      size | count
      -----|------
         1 | 1
         2 | 3
         3 | 16
         4 | 218
  
  Check the numbers [3, 16, 218](http://oeis.org/search?q=3,16,218) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/complete_graph.th
  # Theory Graph
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
         4 | 1
  
  Check the numbers [1, 1, 1](http://oeis.org/search?q=1,1,1) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/cubic_graph.th
  # Theory CubicGraph
  
      size | count
      -----|------
         1 | 0
         2 | 0
         3 | 0
         4 | 1
  
  Check the numbers [0, 0, 1](http://oeis.org/search?q=0,0,1) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/disjoint_cycles.th
  # Theory DisjointCycles
  
      size | count
      -----|------
         1 | 0
         2 | 0
         3 | 1
         4 | 1
  
  Check the numbers [0, 1, 1](http://oeis.org/search?q=0,1,1) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/triangle_free_graph.th
  # Theory GraphWithoutTriangles
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 3
         4 | 7
  
  Check the numbers [2, 3, 7](http://oeis.org/search?q=2,3,7) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/bipartite_graph.th
  # Theory BipartiteGraph
  
      size | count
      -----|------
         1 | 2
         2 | 4
         3 | 8
         4 | 17
  
  Check the numbers [4, 8, 17](http://oeis.org/search?q=4,8,17) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/tricolored_graph.th
  # Theory TriColoredGraph
  
      size | count
      -----|------
         1 | 3
         2 | 9
         3 | 29
         4 | 108
  
  Check the numbers [9, 29, 108](http://oeis.org/search?q=9,29,108) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/involutive_graph.th
  # Theory GraphWithInvolution
  
      size | count
      -----|------
         1 | 1
         2 | 4
         3 | 8
         4 | 32
  
  Check the numbers [4, 8, 32](http://oeis.org/search?q=4,8,32) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/graph_with_Z3_action.th
  # Theory Graph
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 6
         4 | 15
  
  Check the numbers [2, 6, 15](http://oeis.org/search?q=2,6,15) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/strict_poset.th
  # Theory Strict_Poset
  
      size | count
      -----|------
         1 | 1
         2 | 2
         3 | 5
         4 | 16
  
  Check the numbers [2, 5, 16](http://oeis.org/search?q=2,5,16) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/lattice_as_relation.th
  # Theory lattice_as_relation
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
         4 | 2
  
  Check the numbers [1, 1, 2](http://oeis.org/search?q=1,1,2) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/group_inefficient.th
  # Theory group_inefficient
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
         4 | 2
  
  Check the numbers [1, 1, 2](http://oeis.org/search?q=1,1,2) on-line at oeis.org
  

  $ alg --no-source --count --size 1-4 ../../theories/commutative_group_inefficient.th
  # Theory commutative_group_inefficient
  
      size | count
      -----|------
         1 | 1
         2 | 1
         3 | 1
         4 | 2
  
  Check the numbers [1, 1, 2](http://oeis.org/search?q=1,1,2) on-line at oeis.org
  
