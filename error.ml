(* Error reporting. *)

type position = (Lexing.position * Lexing.position) option

exception Error of (position * string * string)

let ksprintf k =
  let k _ =
    let msg = Format.flush_str_formatter () in
    k msg
  in
  Format.kfprintf k Format.str_formatter

let position pos ppf =
  match pos with
  | None -> Format.fprintf ppf "<unknown position>"
  | Some (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol + 1 in
      let end_char = end_pos.Lexing.pos_cnum - end_pos.Lexing.pos_bol in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let end_line = end_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in
      
      if String.length filename != 0 then Format.fprintf ppf "File \"%s\", " filename;
      if begin_line = end_line then
        begin
          Format.fprintf ppf "line %i, " begin_line;
          if begin_char = end_char || begin_char = end_char + 1 then
            Format.fprintf ppf "%i" begin_char
          else
            Format.fprintf ppf "char %i-%i" begin_char end_char
        end
      else
        Format.fprintf ppf "line %i (char %i) - line %i (char %i)" begin_line begin_char end_line end_char

let report (Error.Error (pos, err, msg)) = 
  Format.eprintf "%s error: %s %t@." err msg (Error.position pos) ;
  exit 1


let error ?pos err_type =
  ksprintf (fun msg -> raise (Error (pos, err_type, msg)))

let syntax ?pos = error ?pos "Syntax"
let fatal ?pos = error ?pos "Fatal"
