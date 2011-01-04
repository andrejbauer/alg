(* Silly relation enumeration. *)

let gen_relation n th dodos doundos relation_arr k =
  (* Main loop. *)
  (* r is index of relation, (i,j) current element *)
  let lr = Array.length th.th_relation in
  let rec gen_relation r = function
    | _ when r = lr -> k ()
    | (i,_) when i = n -> gen_relation (r+1) (0,0)
    | (i,j) when j = n -> gen_relation r (i+1,0)
    | (i,j) when relation_arr.(r).(i).(j) = -1 ->
      for k = 0 to 1 do
        relation_arr.(r).(i).(j) <- k ;
        (* check_after_add isn't needed here because fs report back instead *)
        if dodos (r,i,j) r i j && check () then gen_relation r (i,j+1) ;
        doundos (r,i,j) ;
        relation_arr.(r).(i).(j) <- -1
      done
    | (i,j) ->  gen_relation r (i,j+1) in
  gen_relation 0 (0,0)

