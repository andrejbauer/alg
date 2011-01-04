(* Algebras are models of theories. *)

type map_invariant = int array array

type invariant = {
  inv_size : int;
  inv_unary : map_invariant array;
  inv_binary : map_invariant array;
  inv_predicates : int array;
  inv_relations : int array;
}

type algebra = {
  mutable alg_name : string option;
  alg_prod : string list option;
  alg_size : int;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array;
  alg_predicates : int array array;
  alg_relations : int array array array;
}

(* For faster isomorphism checking we define invariants for structures.

   Suppose f : {0,..,n} -> {0,..,n} is a map. For each x in {0,...,n} the sequence

      x_0 = x
      x_{k+1} = f (x_k)

   is eventually periodic, i.e., there are minimal i and j such that 0 <= i < j <= n
   and x_i = f(x_j). We call the pair (i,j) the "eventual period" of x. Given a pair
   (i,j), let N_f(i,j) be the number of elements x whose eventual period is (i,j).
   Then N_f is an invariant for f, i.e., if b : {0,...,n} -> {0,...n} is a bijection
   then N_f = N_{b^{-1} o f o b}.

   We define invariants for the operations and relations of an algebra as follows:

   * for each unary operation f the corresponding invariant is N_f

   * for each binary operation f we define the eventual period (i,j) of x as in the
     case of a map except that we consider the sequence

        x_0 = x
        x_{k+1} = f (x_k, x)

   * for a predicate or relation the corresponding invariant is the number of
     elements or pairs that satisfy it (a better one would be a count of how
     many elements of each in/out degree we have).
*)

exception Result of (int * int)

let unary_invariant f n =
  let t = Array.make (n+1) 0 in
  let eventual_period f x =
    try
      t.(0) <- x ;
      for j = 1 to n do
        t.(j) <- f t.(j-1) ;
        for i = 0 to j-1 do
          if t.(i) = t.(j) then raise (Result (i,j))
        done
      done ;
      Error.fatal "map_invariant: internal error"
    with Result r -> r
  in
  let a = Array.init n (fun j -> Array.make (j+1) 0) in
    for x = 0 to n - 1 do
      let (i,j) = eventual_period f x in
        a.(j-1).(i) <- a.(j-1).(i) + 1
    done ;
    a

let binary_invariant f n =
  let t = Array.make (n+1) 0 in
  let eventual_period f x =
    try
      t.(0) <- x ;
      for j = 1 to n do
        t.(j) <- f x t.(j-1) ;
        for i = 0 to j-1 do
          if t.(i) = t.(j) then raise (Result (i,j))
        done
      done ;
      Error.fatal "map_invariant: internal error"
    with Result r -> r
  in
  let a = Array.init n (fun j -> Array.make (j+1) 0) in
    for x = 0 to n - 1 do
      let (i,j) = eventual_period f x in
        a.(j-1).(i) <- a.(j-1).(i) + 1
    done ;
    a

let predicate_invariant p =
  let k = ref 0 in
    for i = 0 to Array.length p - 1 do
      if p.(i) = 1 then incr k
    done ;
    !k

let relation_invariant r =
  let k = ref 0 in
    for i = 0 to Array.length r - 1 do
      for j = 0 to Array.length r.(i) - 1 do
        if r.(i).(j) = 1 then incr k
      done
    done ;
    !k

let invariant {alg_size=n; alg_unary=us; alg_binary=bs; alg_predicates=ps; alg_relations=rs} =
  { inv_size = n ;
    inv_unary = Array.map (fun u -> unary_invariant (fun k -> u.(k)) n) us;
    inv_binary = Array.map (fun b -> binary_invariant (fun k l -> b.(k).(l)) n) bs;
    inv_predicates = Array.map predicate_invariant ps;
    inv_relations = Array.map relation_invariant rs;
  }



