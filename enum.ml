open Type

(* Enumerate all algebras of a given size for the given theory
   and pass them to the given continuation.
 *)
let enum n {signature={sig_const=const; sig_unary=unary; sig_binary=binary}; axioms=axioms} k =
  (* This is not finished, of course. *)
  for i = 0 to n-1 do
    k { size = n ;
        const = snd (List.fold_left (fun (k,lst) c -> (k+1, (c,k)::lst)) (0,[]) const) ;
        unary = List.map (fun op -> (op, Array.make n i)) unary;
        binary = List.map (fun op -> (op, Array.make_matrix n n i)) binary
      }
  done
