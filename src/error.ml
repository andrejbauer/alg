(** Error reporting. *)

(** Exception [Error (loc, err, msg)] indicates an error of type [err] with
    error message [msg], occurring at position [loc]. *)
exception Error of (Common.position * string * string)

(** [error loc err_type] raises an error of type [err_type]. The [kfprintf] magic allows
    one to write [msg] using a format string. *)
let error ~loc err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
      raise (Error (loc, err_type, msg))
  in
    Format.kfprintf k Format.str_formatter

(** Common error kinds. *)
let unknown_error msg = error ~loc:Common.Nowhere "Error" msg
let internal_error msg = error ~loc:Common.Nowhere "Internal error" msg
let runtime_error msg = error ~loc:Common.Nowhere "Fatal error" msg
let usage_error msg = error ~loc:Common.Nowhere "Usage error" msg
let syntax_error ~loc msg = error ~loc "Syntax error" msg
let typing_error ~loc msg = error ~loc "Typing error" msg
let warning_error ~loc msg = error ~loc "Warning" msg


exception File_error of (Common.position * string * string)

let error1 ~loc err_type =
  let k _ =
    let msg = Format.flush_str_formatter () in
      raise (File_error (loc, err_type, msg))
  in
    Format.kfprintf k Format.str_formatter

let no_file msg = error1 ~loc:Common.Nowhere "File error" msg 