(*Included groups reader/writer and helping functions.*)

let compute_inverses size my_unit binary =
  let rec search k i =
    if k >= size then
      Error.usage_error "an element without an inverse"
    else
      if binary.(i).(k) = my_unit
      then k
      else search (k + 1) i
  in
    Array.init size (search 0)
;;

exception Result of int
exception No_file of string

(*exception No_file of (Common.position * string * string)*)

let find_unit binary size =
  let v = Array.init size (fun k -> k) in
    try 
      Array.iteri
        (fun i w -> if v = w then raise (Result i))
        binary ;
        Error.usage_error "a group without a unit"
    with Result i -> i
;;

(* Convert a list with n * n elements to an array of size n * n *)
let splice n lst =
  let b = Array.make_matrix n n 0 in
  let i = ref 0 in
  let j = ref 0 in
    List.iter (fun x ->
      b.(!i).(!j) <- x ;
      j := !j + 1 ;
      if !j = n then (j := 0 ; i := !i + 1)
    ) lst ;
    b

(*??? Do we want to rename elements, so that 0 is always the unit?*)
let read gs exce = 
  let algebras = ref [] in

  let read_file size =
		try begin
      (*??? Here I have ../groups, because my alg.native is in src. It must be changed to ./, if your alg.native is one level higher.*)
			let ic = open_in ( "../_groups/"^(string_of_int size)) in
			  try
				  while true do
					  let line = input_line ic in
					  let lst = 
              List.map (fun s -> int_of_string s - 1)
                (Str.split (Str.regexp "[ \t]+") line)
            in
			if (List.length lst <> 0) then
				let binary = splice size lst in
						  let my_unit = find_unit binary size in
				let unary = compute_inverses size my_unit binary in
						  let algebra = {
							  Algebra.alg_name = None;
							  Algebra.alg_prod = None;
							  Algebra.alg_size = size;
							  Algebra.alg_const = Array.init (size) (fun i -> i) ;
							  Algebra.alg_unary = [| unary |];
							  Algebra.alg_binary = [| binary |];
							  Algebra.alg_predicates = [| |];
							  Algebra.alg_relations = [| |];
							} in
							algebras := (size, algebra) :: !algebras
					  done
			  with End_of_file -> close_in ic
    end
		with Sys_error msg -> exce "file error (%s)" msg

  in
	  List.iter read_file (List.rev gs) ;
	  !algebras
