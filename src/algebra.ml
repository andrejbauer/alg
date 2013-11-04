(* Algebras are models of theories. *)

(* For faster isomorphism checking we define invariants for structures.

   We have two kinds of invariants: for endo-operations and for operations
   between different sorts.

   Consider an endoperation f : {0,..,n} -> {0,..,n}. For each x in {0,...,n}
   the sequence

      x_0 = x
      x_{k+1} = f (x_k)

   is eventually periodic, i.e., there are minimal i and j such that 0 <= i < j <= n
   and x_i = f(x_j). We call the pair (i,j) the "eventual period" of x. Given a pair
   (i,j), let N_f(i,j) be the number of elements x whose eventual period is (i,j).
   Then N_f is an invariant for f, i.e., if b : {0,...,n} -> {0,...n} is a bijection
   then N_f = N_{b^{-1} o f o b}.

   We define invariants for the operations and relations of an algebra as follows:

   * for a unary endooperation f the corresponding invariant is N_f

   * for a binary endooperation f we define the eventual period (i,j) of x as
     in the unary case except that we consider the sequence

        x_0 = x
        x_{k+1} = f (x_k, x)

     (We could do better if considered pairs (x,y) but we want to keep the invariant
      small.)

   * for a unary or binary operation f which is not an endo-operation, think of it as
     a coloring of the domain. We can count how many elements there are of each color,
     then sort the resulting list in increasing order to get an invariant.

   * for a predicate or relation the corresponding invariant is the number of
     elements or pairs that satisfy it (a better one would be a count of how
     many elements of each in/out degree we have).
*)

type invariant =
  | Endo of int array array (* for each (i,j) we have the corresponding N_f(i,j) *)
  | Nonendo of int array (* in-degrees sorted in ascending order *)

type invariant = {
  inv_size : int array;
  inv_unary : invariant array;
  inv_binary : invariant array;
  inv_predicate : int array;
  inv_relation : (int array * int array) array;
}

(* 
   indegs.(r).(i) is a list of element indices with in degree i in relation r and
   similar for out degrees.
*)
type cache = {
  indegs : int list array array;
  outdegs : int list array array;
}

type algebra = {
  alg_name : string option;
  alg_comment : string list;
  alg_size : int array;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array;
  alg_predicate : int array array;
  alg_relation : int array array array;
}

(* An algebra with all -1's, including the constants. *)
let empty ?nameopt ?(comment=[]) size
    {Syntax.th_const=const;
     Syntax.th_sort=sort;
     Syntax.th_unary=unary;
     Syntax.th_binary=binary;
     Syntax.th_predicate=predicate;
     Syntax.th_relation=relation} =
  {
    alg_name = nameopt;
    alg_comment = comment;
    alg_size = size;
    alg_const = Array.make (Array.length const) (-1);
    alg_unary = Array.map (fun (_, (s, _)) -> Array.make size.(s) (-1)) unary;
    alg_binary = Array.map (fun (_, (s1, s2, _)) -> Array.create_matrix size.(s1) size.(s2) (-1)) binary;
    alg_predicate = Array.map (fun (_, s) -> Array.make size.(s) (-1)) predicate;
    alg_relation = Array.map (fun (_, (s1, s2)) -> Array.create_matrix size.(s1) size.(s2) (-1)) relation
  }

let eventual_period n f x =
  let t = Array.make n (-1) in
  let i = ref 0 in
  let k = ref x in
    while t.(!k) = -1 do
      t.(!k) <- !i ;
      incr i ;
      k := f (!k)
    done ;
    (t.(!k), !i)
    
(* OBSOLETE
exception Result of (int * int)

let eventual_period n f x =
  let t = Array.make (n+1) 0 in
  try
    t.(0) <- x ;
    for j = 1 to n do
      t.(j) <- f t.(j-1) ;
      for i = 0 to j-1 do
        if t.(i) = t.(j) then raise (Result (i,j))
      done
    done ;
    Error.internal_error "algebra.ml -- map_invariant"
  with Result r -> r
*)

let unary_invariant f n1 n2 =
  if n1 = n2 then
  begin
    
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
      Error.internal_error "algebra.ml -- map_invariant"
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
  let outdeg = Array.make (Array.length r) 0 in
  let indeg = Array.make (Array.length r) 0 in
  for i = 0 to Array.length r - 1 do
    for j = 0 to Array.length r.(i) - 1 do
      if r.(i).(j) = 1 then 
        begin
          outdeg.(i) <- outdeg.(i) + 1;
          indeg.(j) <- indeg.(j) + 1
        end
    done
  done ;
  Array.sort compare outdeg; Array.sort compare indeg;
  (indeg, outdeg)
    
let invariant {alg_size=n; alg_unary=us; alg_binary=bs; alg_predicate=ps; alg_relation=rs} = 
  { inv_size = n ;
    inv_unary = Array.map (fun u -> unary_invariant (fun k -> u.(k)) n) us;
    inv_binary = Array.map (fun b -> binary_invariant (fun k l -> b.(k).(l)) n) bs;
    inv_predicates = Array.map predicate_invariant ps;
    inv_relations = Array.map relation_invariant rs;
  } 

let relation_cache r =
  let outdeg = Array.make (Array.length r) 0 in
  let indeg = Array.make (Array.length r) 0 in
  for i = 0 to Array.length r - 1 do
    for j = 0 to Array.length r.(i) - 1 do
      if r.(i).(j) = 1 then 
        begin
          outdeg.(i) <- outdeg.(i) + 1;
          indeg.(j) <- indeg.(j) + 1
        end
    done
  done ;
  (* One vertex can be connected to at most n-1 other + itself *)
  let outdegs = Array.make (Array.length r + 1) [] in
  let indegs = Array.make (Array.length r + 1) [] in
  Array.iteri (fun i a -> outdegs.(a) <- i :: outdegs.(a)) outdeg ;
  Array.iteri (fun i a -> indegs.(a) <- i :: indegs.(a)) indeg ;

  indegs, outdegs

let make_cache {alg_relations=rs} = 
  let rc = Array.map relation_cache rs in
  {indegs = Array.map fst rc; outdegs = Array.map snd rc}

(* if cache is given it must correspond to algebra a.*)
let with_cache ?cache a = let ac = match cache with Some c -> c | None -> make_cache a in
                          (a, ac)

let wo_cache a = fst a
