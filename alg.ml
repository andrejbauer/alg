open Type

let size = ref 3
let noniso = ref false
let irreducible = ref false

(* Command-line options and usage *)
let usage = "Usage: alg --size <n> <theory.th>" ;;

let options = Arg.align [
  ("--help",
    Arg.Unit (fun () -> print_endline usage; exit 0),
    " Print this jelp");
  ("--size",
    Arg.Int (fun n -> size := n),
    " Look for models of this size (default " ^ string_of_int !size ^ ")");
  ("--noniso",
    Arg.Set noniso,
    " Output one algebra of each isomoprhism type");
  ("--irreducible",
    Arg.Set irreducible,
    " Output only irreducible algebras");
] ;;

(* Main program *)

let file = ref None ;;

(* Parse the arguments. Treat the anonymous arguments as files to be read. *)
Arg.parse options
  (fun str -> 
     match !file with
       | None -> file := Some str
       | Some _ -> raise (Arg.Bad " only one theory file should be given"))
  usage ;;


try
  let fh = 
    begin match !file with
      | None -> Error.fatal "please provide a theory file on the command line"
      | Some f -> open_in f
    end in
  let lex = Lexing.from_channel fh in
  let raw_theory = Parser.theory Lexer.token lex in
    close_in fh ;
    let theory = Cook.cook_theory raw_theory in
    let k = ref 0 in
    let names = Print.names !size theory.signature in
      Enum.enum !size theory (fun a -> incr k ; Print.algebra names a) ;
      print_endline ("\nTotal count: " ^ string_of_int !k)
with
    Error.Error (pos, err, msg) -> print_endline (err ^ " error: " ^ msg)
        
