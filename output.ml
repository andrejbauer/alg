(* Output in various formats. *)

module T = Type
module C = Config

type formatter = {
  header: unit -> unit;
  size_header: int -> unit;
  algebra: T.algebra -> unit;
  size_footer: unit -> unit;
  footer: (int * int) list -> unit;
  count_header: unit -> unit;
  count: int -> int -> unit;
  count_footer: (int * int) list -> unit;
  interrupted: unit -> unit                
}

module type TextStyle =
sig
    val names : T.theory -> int -> string array
    val link : string -> string -> string
    val title : out_channel -> string -> unit
    val section : out_channel -> string -> unit
    val footer : out_channel -> unit
    val code : out_channel -> string list -> unit
    val warning : out_channel -> string -> unit
    val algebra_header : out_channel -> string -> string option -> unit
    val algebra_unary : out_channel -> string array -> string -> int array -> unit
    val algebra_binary : out_channel -> string array -> string -> int array array -> unit
    val algebra_footer : out_channel -> unit
    val count_header : out_channel -> unit
    val count_row : out_channel -> int -> int -> unit
    val count_footer : out_channel -> string option -> unit
end

module type Formatter =
sig
  val init : Config.config -> out_channel -> string list -> T.theory -> formatter
end

module Make(S : TextStyle) : Formatter =
struct

  (* Create a URL which queries the http://oeis.org. *)
  let oeis lst =
    let m = List.fold_left (fun m (n,_) -> max m n) 0 lst in
    "http://oeis.org/search?q=" ^
      String.concat ","
      (List.map (fun n -> match Util.lookup n lst with None -> "_" | Some k -> string_of_int k) (Util.enumFromTo 2 m))

  let init
      {C.sizes=sizes; C.source=source}
      ch
      src_lines
      ({T.th_name=th_name; T.th_const=th_const; T.th_unary=th_unary; T.th_binary=th_binary} as th) =

    let names = S.names th (List.fold_left max 0 sizes) in

    let count_footer lst =
      let lst = List.filter (fun (n,_) -> n >= 2) lst in
      S.count_footer ch
        (if List.length lst <= 3
         then None
         else Some (Printf.sprintf "Check the numbers on-line at %s\n" (S.link "OESIS" (oeis lst))))
    in

    { header = 
        begin fun () ->
          S.title ch th_name ;
          if source then S.code ch src_lines
        end;

      size_header =
        begin fun n ->
          S.section ch ("Size " ^ string_of_int n)
        end;

      algebra =
        begin fun {T.alg_name=name; T.alg_prod=prod; T.alg_unary=unary; T.alg_binary=binary} ->
          let name = (match name with | None -> "Model of " ^ th_name | Some n -> n) in
          let info =
            begin match prod with
              | None -> None
              | Some lst -> Some ("Decomposition: " ^ String.concat " * " lst)
            end
          in
          S.algebra_header ch name info ;
          Array.iteri (fun op t -> S.algebra_unary ch names th_unary.(op) t) unary ;
          Array.iteri (fun op t -> S.algebra_binary ch names th_binary.(op) t) binary ;
          S.algebra_footer ch 
        end;

      size_footer = begin fun () -> S.footer ch end;

      count_header = begin fun () -> S.count_header ch end;

      count = S.count_row ch;

      count_footer = count_footer;

      footer =
        begin fun lst ->
          S.section ch "Statistics" ;
          S.count_header ch ;
          List.iter (fun (n,k) -> S.count_row ch n k) lst ;
          count_footer lst
        end;

      interrupted = begin fun () -> S.warning ch "the computation was interrupted by the user" end
    }
end (* Make *)

module MarkdownStyle : TextStyle =
struct
    let names {T.th_const=th_const; T.th_unary=th_unary; T.th_binary=th_binary} n =
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
      let ns =
        Array.init n
          (fun k -> 
            if k < i then th_const.(k)
            else if k - i < j then List.nth default_names (k-i)
            else "x" ^ string_of_int (k-i-j))
      in
      let w = Array.fold_left (fun w s -> max w (String.length s)) 0 ns in
      Array.map (fun s -> (String.make (w - String.length s) ' ') ^ s) ns

    let link txt url = Printf.sprintf "[%s](%s)" txt url

    let title ch str = Printf.fprintf ch "# Theory %s\n\n" str

    let section ch str = Printf.fprintf ch "# %s\n\n" str

    let footer ch = ()

    let code ch lines =
      List.iter (fun line -> Printf.fprintf ch "    %s\n" line) lines ;
      Printf.fprintf ch "\n"
        
    let warning ch msg = Printf.fprintf ch "\n\n**Warning: %s**\n\n" msg

    let algebra_header ch name info =
      Printf.fprintf ch "### %s\n\n" name ;
      match info with
        | None -> ()
        | Some msg -> Printf.fprintf ch "%s\n\n" msg

    let algebra_unary ch names op t =
      let n = Array.length t in
      let w = Array.fold_left (fun w s -> max w (String.length s)) 0 names in
      let v = String.length op in
      let ds = String.make w '-' in
      Printf.fprintf ch "\n    %*s |" (max w v) op ;
      for i = 0 to n-1 do Printf.fprintf ch "  %*s" w names.(i) done ;
      Printf.fprintf ch "\n    %s-+" (String.make (max w v) '-');
      for i = 0 to n-1 do Printf.fprintf ch "--%s" ds done;
      Printf.fprintf ch "\n    %*s |" (max w v) " ";
      for i = 0 to n-1 do Printf.fprintf ch "  %*s" w names.(t.(i)) done ;
      Printf.fprintf ch "\n\n"

    let algebra_binary ch names op t =
      let n = Array.length t in
      let w = Array.fold_left (fun w s -> max w (String.length s)) 0 names in
      let v = String.length op in
      let ds = String.make w '-' in
      Printf.fprintf ch "\n    %*s |" (max w v) op;
      for i = 0 to n-1 do Printf.fprintf ch "  %*s" w names.(i) done ;
      Printf.fprintf ch "\n    %s-+" (String.make (max w v) '-') ;
      for j = 0 to n-1 do Printf.fprintf ch "--%s" ds done ;
      for i = 0 to n-1 do
        Printf.fprintf ch "\n    %*s |" (max w v) names.(i) ;
        for j = 0 to n-1 do
          Printf.fprintf ch "  %*s" w names.(t.(i).(j))
        done
      done ;
      Printf.fprintf ch "\n\n"

    let algebra_footer ch =
      Printf.fprintf ch "\n- - - - - - - - - - - - - - - - - - - - - - - - - - - -\n\n%!" (* flush *)

    let count_header ch =
      Printf.fprintf ch "size | count\n" ;
      Printf.fprintf ch "-----|------\n"

    let count_row ch n k =
      Printf.fprintf ch "%4d | %d\n%!" n k

    let count_footer ch = function
      | None -> Printf.fprintf ch "\n"
      | Some msg -> Printf.fprintf ch "\n%s\n" msg

end

module HTMLStyle : TextStyle =
struct
    let names {T.th_const=th_const; T.th_unary=th_unary; T.th_binary=th_binary} n =
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
        Array.init n
          (fun k -> 
            if k < i then th_const.(k)
            else if k - i < j then List.nth default_names (k-i)
            else "x" ^ string_of_int (k-i-j))

    let link txt url = Printf.sprintf "<a href=\"%s\">%s</a>" url txt

    let title ch str = Printf.fprintf ch "<html>\n<head>\n<title>Theory %s</title>\n</head>\n<body>\n<h1>Theory <tt>%s</tt></h1>\n\n" str str

    let section ch str = Printf.fprintf ch "<h2>%s</h2>\n\n" str

    let footer ch = Printf.fprintf ch "\n</body></html>"

    let code ch lines =
      Printf.fprintf ch "\n<pre>\n" ;
      List.iter (fun line -> Printf.fprintf ch "%s\n" line) lines ;
      Printf.fprintf ch "</pre>\n"
        
    let warning ch msg = Printf.fprintf ch "\n\n<blockquote><b>Warning: %s</b></blockquote>\n\n" msg

    let algebra_header ch name info =
      Printf.fprintf ch "<h3>%s</h3>\n\n" name ;
      match info with
        | None -> ()
        | Some msg -> Printf.fprintf ch "<p>%s</p>\n\n" msg

    let algebra_unary ch names op t =
      let n = Array.length t in
      Printf.fprintf ch "\n<p><table style=\"border-collapse: collapse\" cellpadding=\"5\" border=\"1\">\n<tr><th><code>%s</code></th>" op ;
      for i = 0 to n-1 do Printf.fprintf ch "<th><code>%s</code></th>" names.(i) done ;
      Printf.fprintf ch "</tr>\n<tr><td>&nbsp;</td>" ;
      for i = 0 to n-1 do Printf.fprintf ch "<td><code>%s</code></td>" names.(t.(i)) done ;
      Printf.fprintf ch "</tr>\n</table></p>\n\n"

    let algebra_binary ch names op t =
      let n = Array.length t in
      Printf.fprintf ch "\n<p><table style=\"border-collapse: collapse\"  cellpadding=\"5\" border=\"1\">\n<tr><th><code>%s</code></th>" op;
      for i = 0 to n-1 do Printf.fprintf ch "<th><code>%s</code></th>" names.(i) done ;
      Printf.fprintf ch "</tr>\n" ;
      for i = 0 to n-1 do
        Printf.fprintf ch "<tr><th><code>%s</code></th>" names.(i) ;
        for j = 0 to n-1 do
          Printf.fprintf ch "<td><code>%s</code></td>" names.(t.(i).(j))
        done ;
        Printf.fprintf ch "</tr>\n"
      done ;
      Printf.fprintf ch "</table></p>\n\n"

    let algebra_footer ch = Printf.fprintf ch "\n\n%!"

    let count_header ch =
      Printf.fprintf ch "<table  style=\"border-collapse: collapse\" cellpadding=\"5\" border=\"1\">\n<tr><th>Size</th><th>Count</th></tr>\n"

    let count_row ch n k =
      Printf.fprintf ch "<tr><td align=\"center\"><code>%d</code></td><td align=\"center\"><code>%d</code></td></tr>\n" n k

    let count_footer ch = function
      | None -> Printf.fprintf ch "</table>"
      | Some msg -> Printf.fprintf ch "</table>\n<p>%s</p>\n" msg

end

module Markdown = Make(MarkdownStyle)
module HTML = Make(HTMLStyle)
