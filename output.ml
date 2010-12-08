(* Output in various formats. *)

module T = Type
module C = Config

type formatter = {
  header: unit -> unit;
  size_header: int -> unit;
  algebra: int -> T.algebra -> unit;
  size_footer: int -> int -> unit;
  size_count: int -> int -> unit;
  footer: unit -> unit
}

module type Formatter =
sig
  val init : Config.config -> out_channel -> T.theory -> formatter
end

module Text : Formatter =
struct

  let init
      { C.sizes=sizes }
      ch
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
      Printf.fprintf ch "Theory: %s\n" th_name ;
      Printf.fprintf ch "%s\n\n" (String.make (String.length th_name + 8) '=') ;
      Printf.fprintf ch "Sizes: %s\n\n" (String.concat ", " (List.map string_of_int sizes))
    in

    let size_header n =
      Printf.fprintf ch "Size %d\n" n ;
      Printf.fprintf ch "%s\n\n" (String.make (Util.strlen n + 5) '-')
    in

    let algebra k {T.alg_size=n; T.alg_const=const; T.alg_unary=unary; T.alg_binary=binary} =
      let spaces k = String.make (max 0 k) ' ' in
      let dashes k = String.make (max 0 k) '-' in
        Printf.fprintf ch "%s (size %d, model %d)\n\n" th_name n k ;
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

    let size_count n k =
      Printf.fprintf ch "There are %d algebras of size %d.\n\n" k n
    in

    let size_footer = size_count in

    let footer () = () in

      { header = header;
        size_header = size_header;
        algebra = algebra;
        size_footer = size_footer;
        size_count = size_count;
        footer = footer }
end
