open Type

type position = (Lexing.position * Lexing.position) option

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

(* Missing list functions. *)
let enumFromTo s e =
  let rec
      loop = function
        | n when n <= e -> n :: loop (n+1)
        | _ -> [] in
  loop s

let is_empty = function
  | [] -> true
  | _ -> false

let is_sublist xs ys =
  List.for_all (fun x -> List.mem x ys) xs

let rec
    init = function
      | [] -> []
      | [_] -> []
      | (x::xs) -> x :: init xs

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

let permutations = ref None

(* generate array of all permutations of elements 0..n-1. Cached in permutations. *)
let perms = function
  | n when !permutations = None || fst (fromSome !permutations) <> fac n ->
    let len = fac n in
    let arr = Array.make_matrix len n 0 in
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
        done in
    loop 0;
    permutations := Some (len, arr) ;
    arr
  | _ -> snd (fromSome !permutations)

(* Make fresh copies of operation tables of a given algebra. *)
let copy_algebra {alg_size=n; alg_const=const; alg_unary=unary; alg_binary=binary} =
  { alg_size = n;
    alg_const = const;
    alg_unary = matrix_copy unary;
    alg_binary = array3d_copy binary
  }

(* Combinations without repetition. *)
(*
  Generate next k-combination of elements 0..n-1.
*)
let next_comb n k cur =
  let i = ref 0 in
  while !i < k && cur.(k - !i - 1) >= n - !i - 1 do
    incr i
  done ;
  if !i = k then
    None
  else
    begin
      cur.(k- !i-1) <- cur.(k- !i-1) + 1;
      decr i;
      for j = !i downto 0 do
        cur.(k-j-1) <- cur.(k-j-2) + 1;
      done ;
      Some cur
    end

(*
  Generate all k element subsets of 0..n-1 and pass each set to a given continuation.
*)
let combs n k cont =
  let cur = Array.init k (fun i -> i) in
  let rec loop = function
    | None -> ()
    | Some arr -> cont arr ;
                  loop (next_comb n k cur)
  in loop (Some cur)

(* Combination with repetition. *)
(*
  Generate next k-combination with repetition of elements 0..n-1.
*)
let next_comb_r n k cur =
  let i = ref 0 in
  while !i < k && cur.(k - !i - 1) = n-1 do
    incr i
  done ;
  if !i = k then
    None
  else
    begin
      cur.(k- !i-1) <- cur.(k- !i-1)+1;
      decr i;
      for j = !i downto 0 do
        cur.(k-j-1) <- cur.(k-j-2)
      done ;
      Some cur
    end

(*
  Generate k-combinations with repetition of elements 0..n-1 and
  pass each one to the given continuation.
*)
let combs_r n k cont =
  let cur = Array.make k 0 in
  let rec loop = function
    | None -> ()
    | Some arr -> cont arr ;
                  loop (next_comb_r n k cur)
  in loop (Some cur)

(*
  Generate all k element subsets of the given elements and pass each one to a
  given continuation. Elements are assumed to  be distinct.
*)
let subsets k elems cont =
  let n = Array.length elems in
  let tmp = Array.make k 0 in
  let f arr =
    for i=0 to k-1 do
      tmp.(i) <- elems.(arr.(i));
    done ; cont tmp in
  combs n k f

let print_arr a =
  for i=0 to Array.length a - 1 do
    Printf.printf "%d " a.(i)
  done ; print_endline ""

let print_matrix m = Array.iter print_arr m


(* Auxiliary functions. *)

(* Enumerate a list *)
let enum lst = snd (List.fold_left (fun (k,lst) c -> (k+1, (k,c)::lst)) (0,[]) lst)

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

(* Equivalent to List.for_all f (List.combine xs ys) *)
let for_all_pairs f =
  let rec for_all_pairs' xs ys = 
    match (xs,ys) with
      | ([],_) | (_,[]) -> true
      | (x::xs', y::ys') -> 
        f (x,y) && for_all_pairs' xs' ys'
  in for_all_pairs' 

let rec array_iter2 f arr1 arr2 =
  for i = 0 to Array.length arr1 do
    f arr1.(i) arr2.(i)
  done

(* Return all partitions of n into a product of at least two non decreasing numbers. *)
let partitions n = 
  let rec partitions' n d =
    if n = 1 then [[]]
    else List.concat (List.map (fun k -> List.map (fun ks -> k :: ks) (partitions' (n / k) k))
                        (List.filter (fun k -> n mod k = 0) (enumFromTo d n))) in
  init (partitions' n 2)
