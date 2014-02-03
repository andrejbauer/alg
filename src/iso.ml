open Theory
open Algebra

exception Break
exception Found

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

let check_predicate iso p1 p2 = 
  let l = Array.length iso in
    Util.for_all (fun i -> p1.(i) = p2.(iso.(i))) 0 (l-1)

let check_relation iso r1 r2 =
  let l = Array.length iso in
    Util.for_all2 (fun i j -> r1.(i).(j) = r2.(iso.(i)).(iso.(j))) 0 (l-1) 0 (l-1)

(*XXX:The error is here before the if clause. So that means in the argument.*)
let are_iso {th_const=const_op; th_unary=unary_op; th_binary=binary_op; 
             th_predicates=predicates_op; th_relations=relations_op}
    ({alg_size=n1; alg_const=c1; alg_unary=u1; 
      alg_binary=b1; alg_relations=r1; alg_predicates=p1}, 
     {indegs=indegs1; outdegs=outdegs1})
    ({alg_size=n2; alg_const=c2; alg_unary=u2;
      alg_binary=b2; alg_relations=r2; alg_predicates=p2},
     {indegs=indegs2; outdegs=outdegs2}) = 
  if n1 <> n2
  then false
  else
    begin 
      let n = n1 in
      let lp = Array.length predicates_op in
      let lr = Array.length relations_op in
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
          let f_unary i =
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
            else not (iso.(arr1.(i)) <> arr2.(iso.(i))) in
          let undo i =
            while not (Stack.is_empty stack) && Stack.top stack = i do
              iso.(arr1.(Stack.pop stack)) <- -1 ;
              used.(arr2.(iso.(i))) <- false
            done 
          in 
            (f_unary, undo) in

        let actions_from_binary arr1 arr2 =
          let stack = Stack.create () in
          let f_binary i =
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
            done in (f_binary, undo) in

        let (dos, undos) = List.split (Util.array_map2_list actions_from_unary u1 u2
                                       @ Util.array_map2_list actions_from_binary b1 b2) in

        let check_predicates ps1 ps2 i = 
          Util.for_all (fun j ->  ps1.(j).(i) = ps2.(j).(iso.(i))) 0 (lp-1) in

        let check_relations rs1 rs2 i = 
          Util.for_all2 (fun x y -> iso.(y) = -1 || 
              rs1.(x).(i).(y) = rs2.(x).(iso.(i)).(iso.(y)) &&
              rs1.(x).(y).(i) = rs2.(x).(iso.(y)).(iso.(i))) 0 (lr-1) 0 (n-1) in

        let dos = check_predicates p1 p2 :: check_relations r1 r2 :: dos in

        let allowin = Array.make_matrix lr n [] in
          Array.iteri (fun r -> 
            Array.iteri (fun i -> 
              List.iter (fun x -> 
                allowin.(r).(x) <- indegs2.(r).(i)))) indegs1 ;

          let allowout = Array.make_matrix lr n [] in
            Array.iteri (fun r -> 
              Array.iteri (fun i -> 
                List.iter (fun x -> 
                  allowout.(r).(x) <- Util.intersect allowin.(r).(x) outdegs2.(r).(i)))) outdegs1 ;

            let all = Util.enumFromTo 0 (n-1) in
              
    (* we must set allow to all for the case when there are no relations *)
            let allow = Array.make n all in
              Array.iter (
                Array.iteri (fun i x -> 
                  allow.(i) <- Util.intersect x allow.(i))) allowout ;
              
    (*
      End check when iso is full. Check that it really is an isomorphism.
      Constants need not be checked because they are set independently.
    *)
              let check () =
                let check_op f a1 a2 = Util.for_all_pairs (fun i j -> f iso i j) a1 a2 in
                let us = check_op check_unary u1 u2 in
                let bs = check_op check_binary b1 b2 in
                let ps = check_op check_predicate p1 p2 in
                let rs = check_op check_relation r1 r2 in
                  if us && bs && ps && rs 
                  then raise Found
              in
              let rec gen_iso = function
                | i when i = n -> check ()
                | i when iso.(i) <> -1 -> gen_iso (i+1)
                | i ->
                  List.iter 
                      (fun k -> 
                        if not used.(k) then
                          begin
                            used.(k) <- true ;
                            iso.(i) <- k ;
                            if List.for_all (fun f -> f i) dos then
                              gen_iso (i+1) ;
                            List.iter (fun f -> f i) undos ;
                            iso.(i) <- -1 ;
                            used.(k) <- false
                          end)
                    allow.(i)
              in
                try
                  gen_iso 0 ; false
                with Found -> true
    end
(* Utility functions for checking whether we have already seen a given algebra. *)

let empty_store () = Hashtbl.create 1000

(* Return true if store contains an isomorphic copy of algebra a. Also return
   the invariant for a. *)
let seen th a store =
  let i = invariant (wo_cache a) in
  let lst = (try Hashtbl.find store i with Not_found -> []) in
    List.exists (are_iso th a) lst, i

(* Store the given algebra. Warning: if you pass the optional
   invariant [i] then it _must_ be the same as [invariant a]. This is
   used so that we do not have to recompute invariants. *)
let store s ?inv a = 
  let i = (match inv with Some i -> i | None -> invariant (wo_cache a)) in
  let lst = (try Hashtbl.find s i with Not_found -> []) in
    Hashtbl.replace s i (a::lst)

