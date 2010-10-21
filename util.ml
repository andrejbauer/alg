open Type

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

let fac n = 
  let r = ref 1 in
  for i=2 to n do
    r := !r * i
  done ; !r

(* generate array of all permutations of elements 0..n-1 *)
let perms n =
  let arr = Array.make_matrix (fac n) n 0 in
  let place = ref 0 in
  let used = Array.make n false in
  let cur = Array.make n 0 in
  let rec loop = function
    | k when k = n -> 
      begin 
        for i=0 to n-1 do
          arr.(!place).(i) <- cur.(i);
        done ;
        place := !place + 1
      end
    | k -> 
      for i=0 to n-1 do
        if not used.(i) then
          begin
            used.(i) <- true;
            cur.(k) <- i;
            loop (k+1) ;
            used.(i) <- false
          end
        else ()
      done in loop 0; arr

let copy_algebra {size=n; const=const; unary=unary; binary=binary} = 
  let unaryc = List.map (fun (op, arr) -> (op, Array.copy arr)) unary in
  let binaryc = List.map (fun (op, arr) -> 
                            (op, Array.copy (Array.map Array.copy arr))) binary in
  {size=n; const=const; unary=unaryc; binary=binaryc}
