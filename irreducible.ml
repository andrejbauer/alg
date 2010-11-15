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

  let const = map_combine (uncurry mapping) c1 c2 in

  let unary = map_combine combine_unary u1 u2 in

  let binary = map_combine combine_binary b1 b2 in
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

(* lst is a list of smaller __irreducible__ algebras. It is assumed that List.nth lst k are algebras of size k. *)
let gen_reducible s n lst = 
  if n < 4 then [] (* Avoid undefined behaviour and there are no smaller reducible algebras. *)
  else
    begin
      let arr = Array.map (Array.of_list) (Array.of_list lst) in (* TODO: For faster access. *)
      
      (* Generate all products of algebras which partition into algebras of sizes in partition.
         partition is assumed to be in some order (descending or ascending) order. *)
      let gen_product cont partition = 
        (* last is size of last algebra added to product, start is where to start
           with current algebras (this is only used if we have to multiply two consecutive 
           algebras of the same size), part is the tail of partition *)
        let rec gen_p last start acc = function
          | [] -> cont acc
          | (p::ps) -> 
            let start = if last = p then start else 0 in
            let last = p in
            let ul = Array.length arr.(last) in
            for i=start to ul-1 do
              gen_p last i (product acc arr.(last).(i)) ps
            done in
        if partition = [] then (* This shouldn't happen. *)
          invalid_arg "Empty partition of number."
        else
          begin
            let head = List.hd partition in
            let tail = List.tl partition in 
            let first = arr.(head) in
            Array.iter (fun x -> gen_p head 0 x tail) first
          end in (* end of gen_product *)
      
      let res = ref [] in (* Ugly, I know. *)

      let cont p = 
        res := p :: !res in

      List.iter (gen_product cont) (Util.partitions n) ; !res
    end
