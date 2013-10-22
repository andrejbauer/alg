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
let internal_error ~loc msg = error ~loc "Internal error" msg
let fatal_error ~loc msg = error ~loc "Fatal error" msg
let syntax_error ~loc msg = error ~loc "Syntax error" msg
let typing_error ~loc msg = error ~loc "Typing error" msg
let runtime_error ~loc msg = error ~loc "Runtime error" msg
let warning_error ~loc msg = error ~loc "Warning" msg
