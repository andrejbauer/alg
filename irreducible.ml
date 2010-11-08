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

  (* IMPORTANT: combine_unary and combine_binary assume that algebras are "synced". *)
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

  let const = List.map (uncurry mapping) (List.combine c1 c2) in

  let unary = List.map combine_unary (List.combine u1 u2) in

  let binary = List.map combine_binary (List.combine b1 b2) in
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

(* lst is a list of smaller algebras. It is assumed that List.nth lst k are algebras of size k. *)
let gen_reducible s n lst = 
  let factors = factor n in

  let use_all_pairs l1 l2 start =
    let maybe_add a algs = 
      if seen s a algs then algs else (a::algs) in
    List.fold_left (fun acc left -> 
      List.fold_left (fun acc' right ->
        maybe_add (product left right) acc') 
        acc l2) 
      start l1 in
  List.fold_left (fun acc (k,l) -> use_all_pairs (List.nth lst k) (List.nth lst l) acc) [] factors
