
open Type

open Util

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
   Check if two algebras are isomorphic.
   Basic version. Generates all permutations and then eliminates
   all that are not isomorphisms.
*)
let are_iso {sig_const=const_op; sig_unary=unary_op; sig_binary=binary_op}
            {size=n1; const=c1; unary=u1; binary=b1}
            {size=n2; const=c2; unary=u2; binary=b2} =
  if n1 <> n2 then
    false
  else
    let sortf (a,_) (b,_) = compare a b in
    let c1s = List.sort compare c1 in
    let c2s = List.sort compare c2 in
    let u1s = List.sort sortf u1 in
    let u2s = List.sort sortf u2 in
    let b1s = List.sort sortf b1 in
    let b2s = List.sort sortf b2 in
    let is_isomorphism x = 
      let check_op f a1 a2 = 
        List.for_all (fun ((_,i), (_,j)) -> f x i j) (List.combine a1 a2) in
      List.for_all (fun (i,j) -> check_const x i j) (List.combine c1s c2s) &&
        check_op check_unary u1s u2s &&
        check_op check_binary b1s b2s in
    let perms = perms n1 in
    array_exists is_isomorphism perms

(* 
   Have we already seen an algebra of this isomorphism type. 
*)
let seen s a lst = List.exists (are_iso s a) lst
