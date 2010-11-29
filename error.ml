(* Error reporting. *)

exception Error of (Util.position * string * string)

let ksprintf k =
  let k _ =
    let msg = Format.flush_str_formatter () in
    k msg
  in
  Format.kfprintf k Format.str_formatter

let error ?(pos=None) err_type =
  let k msg = raise (Error (pos, err_type, msg)) in
  ksprintf k

let fatal ?pos = error ?pos "Fatal"
