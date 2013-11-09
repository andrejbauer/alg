(* gebras are models of theories. *)

(* For faster isomorphism checking we define invariants for structures.

   We have two kinds of invariants: for endo-operations and for operations
   between different sorts.

   Consider an endoperation f : {0,..,n} -> {0,..,n}. For each x in {0,...,n}
   the sequence

      x_0 = x
      x_{k+1} = f (x_k)

   is eventually periodic, i.e., there are minimal i and j such that 0 <= i < j <= n
   and x_i = f(x_j). We call the pair (i,j) the "eventual period" of x. If we compute
   the eventual period of every element x and sort the resulting list in lexicographic
   order, we get an invariant.

   We define invariants for the operations and relations of an algebra as follows:

   * for a unary endooperation f the corresponding invariant is the sorted array
     of eventual periods of elements.

   * for a binary endooperation f we define the eventual period (i,j) of x as
     in the unary case except that we consider the sequence

        x_0 = x
        x_{k+1} = f (x_k, x)

     (We could do better if considered pairs (x,y) but we want to keep the invariant
      small.)

   * for a unary or binary operation f which is not an endo-operation, think of it as
     a coloring of the domain. We can count how many elements there are of each color,
     then sort the resulting list in increasing order to get an invariant.

   * for a predicate the invariant is the number of elements that satisfy it.

   * for a binary relation R on A x B, define the degree of x in A to be the number
     of y's such that (x,y) is in R. Similarly define the degree of a y in B.
     The invariant then are the lists of in- and out- degrees of elements, ordered.
*)

type map_invariant =
  | InvariantEndo of int array (* for each element we compute the corresponding eventual period (i,j)
                                  and store i + 1/2 (i + j) (1 + i + j), the pair (i,j) encoded as a number.  *)
  | InvariantNonendo of int array (* in-degrees sorted in ascending order *)

type invariant = {
  inv_size : int array;
  inv_unary : map_invariant array;
  inv_binary : map_invariant array;
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

(* Make fresh copies of operation tables of a given algebra. *)
let copy_algebra a =
  { alg_name = a.alg_name ;
    alg_comment = a.alg_comment ;
    alg_size = a.alg_size ;
    alg_const = Array.copy a.alg_const;
    alg_unary = Util.matrix_copy a.alg_unary;
    alg_binary = Util.array3d_copy a.alg_binary;
    alg_predicate = Util.matrix_copy a.alg_predicate;
    alg_relation = Util.array3d_copy a.alg_relation 
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
    (* encode the eventual period with a single number *)
    let (a, b) = (t.(!k), !i) in
      ((a + b) * (1 + a + b)) lsr 2 + a
    
let unary_endo_invariant u n =
  let t = Array.init n (fun x -> eventual_period n (Array.get u) x) in
    Array.sort Pervasives.compare t ;
    InvariantEndo t

let unary_nonendo_invariant u n1 n2 =
  let t = Array.make n2 0 in
    for i = 0 to n1 - 1 do
      let k = u.(i) in
        t.(k) <- t.(k) + 1
    done ;
    Array.sort Pervasives.compare t ;
    InvariantNonendo t

let binary_endo_invariant b n =
  let t = Array.init n (fun x -> eventual_period n (fun k -> b.(k).(x)) x) in
    Array.sort Pervasives.compare t ;
    InvariantEndo t

let binary_nonendo_invariant b n1 n2 n3 =
  let t = Array.make n3 0 in
    for i = 0 to n1 - 1 do
      for j = 0 to n2 - 1 do
        let k = b.(i).(j) in
          t.(k) <- t.(k) + 1
      done
    done ;
    Array.sort Pervasives.compare t ;
    InvariantNonendo t
    
let predicate_invariant p =
  let k = ref 0 in
    for i = 0 to Array.length p - 1 do
      if p.(i) = 1 then incr k
    done ;
    !k

let relation_invariant r =
  match Array.length r with
    | 0 -> ([| |], [| |])
    | m -> begin match Array.length r.(0) with
        | 0 -> ([| |], [| |])
        | n ->
          let outdeg = Array.make m 0 in
          let indeg = Array.make n 0 in
            for i = 0 to m - 1 do
              for j = 0 to n - 1 do
                if r.(i).(j) = 1 then
                  begin
                    outdeg.(i) <- outdeg.(i) + 1;
                    indeg.(j) <- indeg.(j) + 1
                  end
              done
            done ;
            Array.sort compare outdeg ;
            Array.sort compare indeg ;
            (indeg, outdeg)
    end
    
(* Given a theory and an algebra for it, compute the algebra invariant. *)
let invariant
    {
      Syntax.th_unary=th_unary;
      Syntax.th_binary=th_binary
    }
    { alg_size=size;
      alg_unary=unary;
      alg_binary=binary;
      alg_predicate=predicate;
      alg_relation=relation} = 
  { inv_size = size ;
    inv_unary =
      Array.mapi
        (fun k u -> 
          let (_, (s1, s2)) = th_unary.(k) in
            if s1 = s2 then
              unary_endo_invariant u size.(s1)
            else
              unary_nonendo_invariant u size.(s1) size.(s2))
      unary;
    inv_binary =
      Array.mapi
        (fun k b ->
          let (_, (s1, s2, s3)) = th_binary.(k) in
            if s1 = s2 && s2 = s3 then
              binary_endo_invariant b size.(s1)
            else
              binary_nonendo_invariant b size.(s1) size.(s2) size.(s3))
        binary;
    inv_predicate = Array.map predicate_invariant predicate;
    inv_relation = Array.map relation_invariant relation;
  } 
