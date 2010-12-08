(* Output in various formats. *)

module T = Type
module C = Config

type formatter = {
  header: unit -> unit;
  size_header: int -> unit;
  algebra: int -> T.algebra -> unit;
  size_footer: unit -> unit;
  footer: (int * int) list -> unit;
  count_header: unit -> unit;
  count: int -> int -> unit;
  count_footer: (int * int) list -> unit;
  interrupted: unit -> unit                
}

module type Formatter =
sig
  val init : Config.config -> out_channel -> string list -> T.theory -> formatter
end

(* Create a URL which queries the http://oeis.org. *)
let oeis lst =
  let m = List.fold_left (fun m (n,_) -> max m n) 0 lst in
  "http://oeis.org/search?q=" ^
    String.concat ","
    (List.map (fun n -> match Util.lookup n lst with None -> "_" | Some k -> string_of_int k) (Util.enumFromTo 2 m))
;;

module Text : Formatter =
struct

  let init
      {C.sizes=sizes; C.source=source}
      ch
      src_lines
      {T.th_name=th_name; T.th_const=th_const; T.th_unary=th_unary; T.th_binary=th_binary} =

    let names =
      let n = List.fold_left max 0 sizes in
      let forbidden_names = Array.to_list th_const @ Array.to_list th_unary @ Array.to_list th_binary in
      let default_names = 
        List.filter (fun x -> not (List.mem x forbidden_names))
          ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
           "n"; "o"; "p"; "q"; "e"; "r"; "s"; "t"; "u"; "v"; "x"; "y"; "z";
           "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I"; "J"; "K"; "L"; "M";
           "N"; "O"; "P"; "Q"; "R"; "S"; "T"; "U"; "V"; "W"; "X"; "Y"; "Z"]
      in
      let i = Array.length th_const in
      let j = List.length default_names in
      let pad = String.make (if n > i + j then 1 else 0) ' ' in
        Array.init n (fun k -> 
                        if k < i then pad ^ th_const.(k)
                        else if k - i < j then pad ^ List.nth default_names (k-i)
                        else "x" ^ string_of_int (k-i-j))
    in
        
    let header () =
      Printf.fprintf ch "# Theory: %s\n\n" th_name ;
      if source then begin
        List.iter (fun line -> Printf.fprintf ch "    %s\n" line) src_lines ;
        Printf.fprintf ch "\n"
      end
    in

    let size_header n =
      Printf.fprintf ch "## Size %d\n\n" n ;
    in

    let algebra k {T.alg_size=n; T.alg_name=name; T.alg_prod=prod; T.alg_const=const; T.alg_unary=unary; T.alg_binary=binary} =
      let spaces k = String.make (max 0 k) ' ' in
      let dashes k = String.make (max 0 k) '-' in
        Printf.fprintf ch "%s%s\n\n"
          (match name with Some n -> n | None -> "")
          (match prod with None -> "" | Some lst -> " (" ^ String.concat " * " lst ^ ")") ;
        Array.iteri (fun op t ->
                       Printf.fprintf ch "     %s |" th_unary.(op) ;
                       for i = 0 to n-1 do Printf.fprintf ch " %s " names.(i) done ;
                       Printf.fprintf ch "\n    %s+" (dashes (String.length th_unary.(op) + 2)) ;
                       for i = 0 to n-1 do Printf.fprintf ch "---" done;
                       Printf.fprintf ch "\n    %s|" (spaces (String.length th_unary.(op) + 2)) ;
                       for i = 0 to n-1 do Printf.fprintf ch " %s " names.(t.(i)) done ;
                       Printf.fprintf ch "\n"
                    ) unary ;
        Array.iteri (fun op t -> 
                       let sp = spaces (String.length th_binary.(op) - 1) in
                       let ds = dashes (String.length th_binary.(op) + 2) in
                         Printf.fprintf ch "\n\n     %s |" th_binary.(op) ;
                         for i = 0 to n-1 do Printf.fprintf ch " %s " names.(i) done ;
                         Printf.fprintf ch "\n    %s+" ds ;
                         for j = 0 to n-1 do Printf.fprintf ch "---" done ;
                         for i = 0 to n-1 do
                           Printf.fprintf ch "\n     %s%s |" sp names.(i) ;
                           for j = 0 to n-1 do
                             Printf.fprintf ch " %s " names.(t.(i).(j))
                           done
                         done ;
                   Printf.fprintf ch "\n"
                    ) binary ;
        Printf.fprintf ch "\n- - - - - - - - - - - - - - - - - - - - - - - - - - - -\n\n%!" (* flush *)
    in

    let size_footer () = () in

    let count_header () =
      Printf.fprintf ch "    size | count\n" ;
      Printf.fprintf ch "    -----+------\n"
    in

    let count n k =
      Printf.fprintf ch "    %4d | %d\n%!" n k
    in

    let count_footer lst =
      let lst = List.filter (fun (n,_) -> n >= 2) lst in
      if List.length lst > 3 then Printf.fprintf ch "\nCheck the numbers on-line at [OEIS](%s)\n" (oeis lst) ;
      Printf.fprintf ch "\n"
    in

    let footer lst = 
      Printf.fprintf ch "## Total counts:\n\n" ;
      count_header () ;
      List.iter (fun (n,k) -> count n k) lst ;
      count_footer lst
    in

    let interrupted () =
      Printf.fprintf ch "\n\n**Warning: the computation was interrupted by the user.**\n\n"
    in

      { header = header;
        size_header = size_header;
        algebra = algebra;
        size_footer = size_footer;
        count_header = count_header ;
        count = count;
        footer = footer;
        count_footer = count_footer;
        interrupted = interrupted
      }

end
