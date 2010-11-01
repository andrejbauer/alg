
open Type

open Util

exception Break

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


let are_iso {sig_const=const_op; sig_unary=unary_op; sig_binary=binary_op}
            {size=n1; const=c1; unary=u1; binary=b1}
            {size=n2; const=c2; unary=u2; binary=b2} =
  if n1 <> n2 then false
  else 
    let sortf (a,_) (b,_) = compare a b in
    let c1s = List.sort compare c1 in
    let c2s = List.sort compare c2 in
    let u1s = List.sort sortf u1 in
    let u2s = List.sort sortf u2 in
    let b1s = List.sort sortf b1 in
    let b2s = List.sort sortf b2 in
    let n = n1 in
    let used = Array.make n false in
    let iso = Array.make n (-1) in
    (* Handle constants *)
    List.iter (fun (i,j) -> used.(j) <- true ; iso.(i) <- j) (List.combine c1s c2s) ;
    
    (* 
       Generate actions from unary and binary operations analogous to generation
       of actions from axioms. Axioms here are implicit from the definition of isomorphism
    *)
    let actions_from_unary ((_, arr1), (_, arr2)) =
      let stack = Stack.create () in
      let f i =
        if iso.(arr1.(i)) = -1 then
          begin
            iso.(arr1.(i)) <- arr2.(iso.(i)) ;
            Stack.push i stack ; true
          end
        else if iso.(arr1.(i)) <> arr2.(iso.(i)) then
          false
        else true in
      let undo i = 
        while not (Stack.is_empty stack) && let ii = Stack.top stack in i = ii do
          iso.(arr1.(Stack.pop stack)) <- -1
        done in (f, undo) in

    let actions_from_binary ((_, arr1), (_, arr2)) =
      let stack = Stack.create () in
      let f i =
        try
          for k=0 to n-1 do
            if iso.(k) <> -1 then
              begin
                if iso.(arr1.(i).(k)) = -1 then
                  begin
                    iso.(arr1.(i).(k)) <- arr2.(iso.(i)).(iso.(k)) ;
                    Stack.push (i, arr1.(i).(k)) stack
                  end
                else if iso.(arr1.(i).(k)) <> arr2.(iso.(i)).(iso.(k)) then
                  raise Break ;

                if iso.(arr1.(k).(i)) = -1 then
                  begin
                    iso.(arr1.(k).(i)) <- arr2.(iso.(k)).(iso.(i)) ;
                    Stack.push (i, arr1.(k).(i)) stack
                  end
                else if iso.(arr1.(k).(i)) <> arr2.(iso.(k)).(iso.(i)) then
                  raise Break
              end
          done ; true
        with Break -> false in
      let undo i = 
        while not (Stack.is_empty stack) && i = fst (Stack.top stack) do
          iso.(snd (Stack.pop stack)) <- -1
        done in (f, undo) in
    
    let (dos, undos) = List.split (List.map actions_from_unary (List.combine u1s u2s)
                                   @ List.map actions_from_binary (List.combine b1s b2s)) in


    (*
      End check when iso is full. Check that it really is an isomorphism. 
      Constants need not be checked because they are set independently.
    *)
    let check () = 
      let check_op f a1 a2 = 
        List.for_all (fun ((_,i), (_,j)) -> f iso i j) (List.combine a1 a2) in
      if check_op check_unary u1s u2s && check_op check_binary b1s b2s then
        raise Break in

    let rec gen_iso = function
      | i when i = n -> check ()
      | i when iso.(i) <> -1 -> gen_iso (i+1)
      | i -> 
        for k=0 to n-1 do
          if not used.(k) then
            begin
              used.(k) <- true ;
              iso.(i) <- k ;
              if List.for_all (fun f -> f i) dos then
                gen_iso (i+1) ;
              List.iter (fun f -> f i) undos ;
              iso.(i) <- -1 ;
              used.(k) <- false
            end
        done in
    try
      gen_iso 0 ; false
    with Break -> true
    
(* 
   Have we already seen an algebra of this isomorphism type. 
*)
let seen s a lst = List.exists (are_iso s a) lst
