open Type
open Util

open Iso

(* It is assumed that the two algebras correspond to the same signature. *)
(* Note that this returns an algebra not in a form where supplied constants come before
   other elements. TODO: We cannot print this algebra correctly with current implementation of Print module. *)
let product {size=n1; const=c1; unary=u1; binary=b1}
            {size=n2; const=c2; unary=u2; binary=b2} =
  let size = n1 * n2 in
  let mapping i j = n2 * i + j in

  let combine_unary ((op1, arr1), (op2, arr2)) =
    let arr = Array.make size 0 in
    for k=0 to n1-1 do
      for l=0 to n2-1 do
        arr.(mapping k l) <- mapping arr1.(k) arr2.(l)
      done
    done ; (op1, arr) in


  let combine_binary ((op1, arr1), (op2, arr2)) =
    let arr = Array.make_matrix size size 0 in
    for k=0 to n1-1 do
      for l=0 to n2-1 do
        for i=0 to n1-1 do
          for j=0 to n2-1 do
            arr.(mapping k l).(mapping i j) <- mapping arr1.(k).(i) arr2.(l).(j)
          done
        done
      done
    done ; (op1, arr) in

  (* This is just a safeguard. Lists should already be sorted. *)
  let sortf (a,_) (b,_) = compare a b in
  let c1s = List.sort compare c1 in
  let c2s = List.sort compare c2 in
  let u1s = List.sort sortf u1 in
  let u2s = List.sort sortf u2 in
  let b1s = List.sort sortf b1 in
  let b2s = List.sort sortf b2 in

  let const = List.map (uncurry mapping) (List.combine c1s c2s) in

  let unary = List.map combine_unary (List.combine u1s u2s) in

  let binary = List.map combine_binary (List.combine b1s b2s) in
  {size=size; const=const; unary=unary; binary=binary}

let factor n =
  let rec
      factor' acc = function
        | k when k * k > n -> acc
        | k when n mod k = 0 -> factor' ((k,n / k)::acc) (succ k)
        | k -> factor' acc (succ k) in
  factor' [] 2

let is_reducible s a lst =
  let factors = factor a.size in
  let exist_factors (k,l) =
    let ks = List.nth lst k in
    let ls = List.nth lst l in
    List.exists (fun left -> List.exists (fun right -> are_iso s a (product left right)) ls) ks in
  List.exists exist_factors factors
