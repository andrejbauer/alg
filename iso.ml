open Type

exception Break
exception Found

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
  Util.for_all (fun i -> iso.(u1.(i)) = u2.(iso.(i))) 0 (l-1)

(*
  Checks if binary operation is multiplicative.
*)
let check_binary iso b1 b2 =
  let l = Array.length iso in
  Util.for_all2 (fun i j -> iso.(b1.(i).(j)) = b2.(iso.(i)).(iso.(j))) 0 (l-1) 0 (l-1)


let are_iso {th_const=const_op; th_unary=unary_op; th_binary=binary_op}
            {alg_size=n1; alg_const=c1; alg_unary=u1; alg_binary=b1}
            {alg_size=n2; alg_const=c2; alg_unary=u2; alg_binary=b2} =
  if n1 <> n2 then false
  else
    let n = n1 in
    let used = Array.make n false in
    let iso = Array.make n (-1) in
    (* Handle constants *)
    Util.array_iter2 (fun i j -> used.(j) <- true ; iso.(i) <- j) c1 c2 ;

    (*
       Generate actions from unary and binary operations analogous to generation
       of actions from axioms. Axioms here are implicit from the definition of isomorphism
      IMPORTANT: actions_from_unary and actions_from_binary assume that algebras
      are "synced".
    *)
    let actions_from_unary arr1 arr2 =
      let stack = Stack.create () in
      let f i =
        if iso.(arr1.(i)) = -1 then
          begin
            if used.(arr2.(iso.(i))) then
              false
            else
              begin
                iso.(arr1.(i)) <- arr2.(iso.(i)) ;
                used.(arr2.(iso.(i))) <- true ;
                Stack.push i stack ; true
              end
          end
        else if iso.(arr1.(i)) <> arr2.(iso.(i)) then
          false
        else true in
      let undo i =
        while not (Stack.is_empty stack) && Stack.top stack = i do
          iso.(arr1.(Stack.pop stack)) <- -1 ;
          used.(arr2.(iso.(i))) <- false
        done in (f, undo) in

    let actions_from_binary arr1 arr2 =
      let stack = Stack.create () in
      let f i =
        try
          for k=0 to n-1 do
            if iso.(k) <> -1 then
              begin
                if iso.(arr1.(i).(k)) = -1 then
                  begin
                    if used.(arr2.(iso.(i)).(iso.(k))) then
                      raise Break ;

                    iso.(arr1.(i).(k)) <- arr2.(iso.(i)).(iso.(k)) ;
                    used.(arr2.(iso.(i)).(iso.(k))) <- true ;
                    Stack.push (i, (arr1.(i).(k), arr2.(iso.(i)).(iso.(k)))) stack
                  end
                else if iso.(arr1.(i).(k)) <> arr2.(iso.(i)).(iso.(k)) then
                  raise Break ;

                if iso.(arr1.(k).(i)) = -1 then
                  begin
                    if used.(arr2.(iso.(k)).(iso.(i))) then
                      raise Break ;

                    iso.(arr1.(k).(i)) <- arr2.(iso.(k)).(iso.(i)) ;
                    used.(arr2.(iso.(k)).(iso.(i))) <- true ;
                    Stack.push (i, (arr1.(k).(i), arr2.(iso.(k)).(iso.(i)))) stack
                  end
                else if iso.(arr1.(k).(i)) <> arr2.(iso.(k)).(iso.(i)) then
                  raise Break
              end
          done ; true
        with Break -> false in
      let undo i =
        while not (Stack.is_empty stack) && i = fst (Stack.top stack) do
          let (_, (a,b)) = Stack.pop stack in
          iso.(a) <- -1 ;
          used.(b) <- false
        done in (f, undo) in

    let (dos, undos) = List.split (Util.array_map2_list actions_from_unary u1 u2
                                   @ Util.array_map2_list actions_from_binary b1 b2) in

    (*
      End check when iso is full. Check that it really is an isomorphism.
      Constants need not be checked because they are set independently.
    *)
    let check () =
      let check_op f a1 a2 = Util.for_all_pairs (fun i j -> f iso i j) a1 a2
      in
        if check_op check_unary u1 u2 && check_op check_binary b1 b2 then
          raise Found
    in

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
    with Found -> true

(*
   Have we already seen an algebra of this isomorphism type.
*)
let seen s a lst = List.exists (are_iso s a) lst
