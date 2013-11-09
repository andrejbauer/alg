module IntMap =
  Map.Make(struct
    type t = int
    let compare = compare
  end) ;;

(* Return the list of lines in the given file. *)
let read_lines filename =
  let fh = open_in filename in
  let lines = ref [] in
  begin try
          while true do
            let line = input_line fh in
            lines := line :: !lines ;
          done
    with End_of_file -> close_in fh
  end ;
  List.rev !lines

(* Return the filename extension or "" if there isn't one. *)
let filename_extension filename =
  let fn = Filename.basename filename in
    try
      let k = String.rindex fn '.' in
        String.sub fn (k+1) (String.length fn - k - 1)
    with Not_found -> ""

(* The number of characters an non-negative int takes to print out. *)
let rec strlen = function
  | k when k < 10 -> 1
  | k -> 1 + strlen (k / 10)

(* Return a duplicate element in the list, if one exists. *)
let rec find_duplicate = function
  | [] -> None
  | x :: xs -> if List.mem x xs then Some x else find_duplicate xs

(* Associative list lookup without exceptions. *)
let lookup x lst =
  try
    Some (List.assoc x lst)
  with Not_found -> None

(* A combination of map and filter *)
let rec filter_map f = function
  | [] -> []
  | x::xs ->
      begin match f x with
        | None -> filter_map f xs
        | Some y -> y :: filter_map f xs
      end

(* Lists as sets. *)
let rec union lst1 lst2 =
  match lst1, lst2 with
    | [], lst2 -> lst2
    | lst1, [] -> lst1
    | x::xs, ys ->
        if List.mem x ys
        then union xs ys
        else x :: union xs ys

(* Lists as sets. *)
let rec union lst1 lst2 =
  match lst1, lst2 with
    | [], lst2 -> lst2
    | lst1, [] -> lst1
    | x::xs, ys ->
        if List.mem x ys
        then union xs ys
        else x :: union xs ys

let rec remove x = function
  | [] -> []
  | y::ys ->
      if x = y then ys
      else y :: remove x ys

let rec remove_many xs = function
  | [] -> []
  | y :: ys ->
    if List.mem y xs then ys
    else y :: remove_many xs ys

let intersect lst1 lst2 =
  List.fold_left (fun acc a -> if List.mem a lst2 then a::acc else acc) [] lst1

(* Missing array functions. *)
let array_for_all p a =
  let n = Array.length a in
  let rec check k = (k >= n) || (p a.(k) && check (k+1)) in
    check 0

let matrix_for_all p a =
  array_for_all (fun r -> array_for_all p r) a

let array_exists p a =
  let n = Array.length a in
  let rec check k = (k < n) && (p a.(k) || check (k+1)) in
    check 0

let matrix_forall p a =
  array_exists (fun r -> array_exists p r) a

let matrix_copy a =
  Array.init (Array.length a) (fun k -> Array.copy a.(k))

let array3d_copy a =
  Array.init (Array.length a) (fun k -> matrix_copy a.(k))

let array_map2 f a1 a2 =
  let n = Array.length a1 in
    if n <> Array.length a2
    then failwith "array_map2: invalid argument"
    else
      Array.init n (fun i -> f a1.(i) a2.(i))

let array_map2_list f a1 a2 =
  let n = Array.length a1 in
    if n <> Array.length a2
    then failwith "array_map2: invalid argument"
    else
      let lst = ref [] in
        for i = 0 to n-1 do
          lst := f a1.(i) a2.(i) :: !lst
        done ;
        List.rev !lst

let rec array_iter2 f arr1 arr2 =
  for i = 0 to Array.length arr1 - 1 do
    f arr1.(i) arr2.(i)
  done

(* Missing list functions. *)
let enumFromTo s e =
  let rec loop = function
    | n when n <= e -> n :: loop (n+1)
    | _ -> []
  in
    loop s

(* Like List.map with indices. *)
let map_enum f lst =
  let rec loop i = function
    | [] -> []
    | x::xs -> (f i x) :: loop (i+1) xs
  in
    loop 0 lst

(* Like List.iter with indices *)
let iter_enum f lst =
  let rec loop i = function
    | [] -> ()
    | x::xs -> (f i x) ; loop (i+1) xs
  in
    loop 0 lst

let is_empty = function
  | [] -> true
  | _ -> false

let is_sublist xs ys =
  List.for_all (fun x -> List.mem x ys) xs

let rec replicate n a =
  if n = 0 then [] else a :: replicate (n-1) a

let rev_combine xs ys = 
  let rec rev_combine' acc xs ys =
    match (xs,ys) with
      | ([],_) | (_,[]) -> acc
      | (x::xs',y::ys') -> rev_combine' ((x,y) :: acc) xs' ys'
  in rev_combine' [] xs ys

let rev_take n xs = 
  let rec rev_take acc n = function
    | [] -> acc
    | (x::xs) when n = 0 -> acc
    | (x::xs) -> rev_take (x::acc) (n-1) xs in
  rev_take [] n xs

let rec split x = function
  | [] -> ([],[])
  | (y::ys) as ys' when y <> x -> ([], ys')
  | (y::ys) -> let (xs', ys') = split x ys
               in (y::xs', ys')

let rec group = function
  | [] -> []
  | (x::xs) -> let (xs', ys) = split x xs
               in (x, List.length xs') :: group ys

let fromSome = function
  | (Some a) -> a
  | _ -> invalid_arg "fromSome called with None argument"

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

let alg_prod a1 a2 i1 i2 =
  match a1, a2, i1, i2 with
    | _, _, Some lst1, Some lst2 -> Some (lst1 @ lst2)
    | Some i1, _, None, Some lst2 -> Some (i1 :: lst2)
    | _, Some i2, Some lst1, None -> Some (lst1 @ [i2])
    | Some i1, Some i2, None, None -> Some [i1; i2]
    | _, _, _, _ -> None

let print_arr a =
  for i=0 to Array.length a - 1 do
    Printf.printf "%d " a.(i)
  done ; print_endline ""

let print_matrix m = Array.iter print_arr m


(* Auxiliary functions. *)

(* Enumerate a list, return the number of elements and the enumerated list. *)
let enum lst = List.fold_left (fun (k,lst) c -> (k+1, (c,k)::lst)) (0,[]) lst

(* Invert assoc list. *)
let invert xs = List.map (fun (a,b) -> (b,a)) xs

(* Various foralls and exists *)

(* Check function for all elements in range i - j *)
let for_all f i j =
  let rec
      loop c = (c > j) || f c && loop (c + 1)
  in loop i

(* Check function for all elements in range i - j and k - l *)
let for_all2 f i j k l = for_all (fun x -> for_all (f x) k l) i j

(* Dual to for_all *)
let exists f i j =
  let rec loop c = (c <= j) && (f c || loop (c + 1))
  in loop i

(* Dual to for_all2 *)
let exists2 f i j k l = exists (fun x -> exists (f x) k l) i j


(* Equivalent to List.for_all f (List.combine xs ys) but works with arrays *)
let for_all_pairs f xs ys =
  let n = Array.length xs in
    if n <> Array.length ys then
      failwith "for_all_pairs: invalid arguments"
    else 
      let b = ref true in
      let i = ref 0 in
        while !b && !i < n do
          b := f xs.(!i) ys.(!i) ;
          incr i
        done ;
        ! b

(* Divisors of a number without the number itself, sorted by size *)
let divisors n =
  let rec loop k acc1 acc2 =
    if k * k > n then List.rev acc1 @ acc2
    else if k * k = n then List.rev acc1 @ (k :: acc2)
    else if n mod k = 0 then loop (k+1) (k :: acc1) ((n / k) :: acc2)
    else loop (k+1) acc1 acc2
  in
    loop 2 [] []

(* Small divisors of n larger than 1, i.e., those not exceeding the square root of n. *)
let rec small_divisors n =
  let rec loop k =
    if k * k > n then []
    else if n mod k = 0 then k :: loop (k+1)
    else loop (k+1)
  in
    loop 2
      
(* Return all partitions of n into a product of at least two non-decreasing numbers. *)
let partitions n =
  let rec part n = function
    | [] -> []
    | (d::ds) as lst when n mod d = 0 && d * d <= n ->
        let m = n/d in ([d;m] :: (List.map (fun p -> d :: p) (part m lst))) @ (part n ds)
    | _::ds -> part n ds
  in
    part n (small_divisors n)

let apply_to_snd f (_,t) = f t
