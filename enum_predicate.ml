(* Silly predicate enumeration. *)

let gen_predicate n th predicate_arr k =
  let lp = Array.length th.th_predicates in
  let rec gen_predicate i = function
    | j when j = n && i < lp - 1 -> gen_predicate (i+1) 0
    | j when j = n || i = lp -> k ()
    | j when predicate_arr.(i).(j) = -1 ->
        for b = 0 to 1 do
          predicate_arr.(i).(j) <- b ;
          if dodos (i,j) then gen_predicate i (j+1) ;
          doundos (i,j) ;
          predicate_arr.(i).(j) <- -1 ;
        done
    | j -> gen_predicate i (j+1)
  in gen_predicate 0 0


