open Theory
open Algebra
open Util

module FO=First_order

(* Evaluate equation in the context of vars. 
   operation arrays are assumed to be fully filled.
*)
let eval_eq alg vars (left,right) = 
  (Eval.eval_term alg vars left, Eval.eval_term alg vars right)

(* Naive check if model satisfies all axioms. *)
let check_model {th_equations=equations; th_axioms=axioms} alg =
  let n = alg.alg_size in 
  let check_eq (num_vars, eq) = 
    array_for_all 
      (fun vars -> let (rl, rr) = eval_eq alg vars eq in rl = rr)
      (ntuples n num_vars) in
  List.for_all check_eq equations && List.for_all (FO.check_formula alg) axioms


(* Naive checking of isomorphisms. *)

(* generate array of all permutations of elements 0..n-1. *)
let perms n = 
  let len = fac n in
  let arr = Array.make_matrix len n 0 in
  let place = ref 0 in
  let used = Array.make n false in
  let cur = Array.make n 0 in
  let rec loop = function
    | k when k = n -> 
      begin 
        for i=0 to n-1 do
          arr.(!place).(i) <- cur.(i);
        done ;
        place := !place + 1
      end
    | k -> 
      for i=0 to n-1 do
        if not used.(i) then
          begin
            used.(i) <- true;
            cur.(k) <- i;
            loop (k+1) ;
            used.(i) <- false
          end
      done in 
  loop 0; arr

(*
  Checks if permutation preserves constants.
*)
let check_const iso c1 c2 = iso.(c1) = c2

(*
  Checks if a function commutes with permutation.
  f(i(a)) = i(f(a)).
*)
let check_unary iso u1 u2 =
  let l = Array.length iso in 
  for_all (fun i -> iso.(u1.(i)) = u2.(iso.(i))) 0 (l-1)

(*
  Checks if binary operation is multiplicative.
*)
let check_binary iso b1 b2 = 
  let l = Array.length iso in
  for_all2 (fun i j -> iso.(b1.(i).(j)) = b2.(iso.(i)).(iso.(j))) 0 (l-1) 0 (l-1)

(*
  Check if predicates are isomorphic for iso.
*)
let check_predicate iso p1 p2 = 
  let l = Array.length iso in
  Util.for_all (fun i -> p1.(i) = p2.(iso.(i))) 0 (l-1)

(*
  Check if relations are isomorphic for iso.
*)
let check_relation iso r1 r2 =
  let l = Array.length iso in
  Util.for_all2 (fun i j -> r1.(i).(j) = r2.(iso.(i)).(iso.(j))) 0 (l-1) 0 (l-1)

(* 
   Check if two algebras are isomorphic.
   Basic version. Generates all permutations and then eliminates
   all that are not isomorphisms.
*)
let are_iso th
            {alg_size=n1; alg_const=c1; alg_unary=u1;
             alg_binary=b1; alg_predicates=p1; alg_relations=r1}
            {alg_size=n2; alg_const=c2; alg_unary=u2;
             alg_binary=b2; alg_predicates=p2; alg_relations=r2} =
  if n1 <> n2 then
    false
  else
    let is_isomorphism x = 
      let p = ref true in
      let i = ref 0 in
      while !i < Array.length th.th_const && !p do
        p := check_const x c1.(!i) c2.(!i) ;
        incr i
      done ;
      i := 0 ;
      while !i < Array.length th.th_unary && !p do
        p := check_unary x u1.(!i) u2.(!i) ;
        incr i
      done ;
      i := 0 ;
      while !i < Array.length th.th_binary && !p do
        p := check_binary x b1.(!i) b2.(!i) ;
        incr i
      done ; 
      i := 0 ;
      while !i < Array.length th.th_predicates && !p do
        p := check_predicate x p1.(!i) p2.(!i) ;
        incr i
      done ;
      i := 0 ;
      while !i < Array.length th.th_relations && !p do
        p := check_relation x r1.(!i) r2.(!i) ;
        incr i
      done ; !p in
    let perms = perms n1 in
    array_exists is_isomorphism perms

(* 
   Have we already seen an algebra of this isomorphism type. 
*)
let seen theory alg lst = List.exists (fun (alg',_) -> are_iso theory alg alg') lst
