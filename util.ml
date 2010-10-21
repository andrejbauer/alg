(*
  Generating all ntuples.
*)
let exp_int a = function
  | b when b <= 0 -> 1
  | b ->   
    let rec loop = function
      | n when n = 1 -> a
      | n when n mod 2 = 0 -> let t = loop (n / 2) in t * t
      | n -> let t = loop (n / 2) in t * t * a
    in loop b

(* generate array of all n tuples with elements from 0..j-1 *)
let ntuples j n =
  let arr = Array.make_matrix (exp_int j n) n 0 in
  let place = ref 0 in
  let rec loop = function
    | k when k = n -> place := !place + 1
    | k -> for i=0 to j-1 do
        begin
          let start = !place in
          begin
            loop (k+1) ;
            for j=start to !place-1 do
              arr.(j).(k) <- i
            done
          end
        end
      done in loop 0 ; arr

