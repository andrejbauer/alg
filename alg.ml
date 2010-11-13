open Type

open Iso

open Irreducible

open Util

let size = ref 3
let irreducible = ref false
let count_only = ref false

(* Command-line options and usage *)
let usage = "Usage: alg --size <n> <theory.th>" ;;

let options = Arg.align [
  ("--help",
    Arg.Unit (fun () -> print_endline usage; exit 0),
    " Print this jelp");
  ("--size",
    Arg.Int (fun n -> size := n),
    " Look for models of this size (default " ^ string_of_int !size ^ ")");
  ("--count",
    Arg.Set count_only,
    " Just count the models, do not print them out.");
  ("--irreducible",
    Arg.Set irreducible,
    " Output only irreducible algebras.");
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
    let unique = ref [] in
    let names = Print.names !size theory.signature in
    if !size < List.length (theory.signature.sig_const) then
      Error.fatal "There are more constants than the required size of the models."
    else 
      begin
        if not !irreducible then
          begin
            let cont a =
              if not (seen theory.signature a !unique) then
                begin
                  incr k;
                  unique := (copy_algebra a) :: !unique ;
                  if not !count_only then
                    Print.algebra names
                      (Util.invert (Util.enum_ops theory.signature.sig_unary))
                      (Util.invert (Util.enum_ops theory.signature.sig_binary))
                      a
                end
            in
            Enum.enum !size theory cont ;
            print_endline ("\nTotal count: " ^ string_of_int !k)
          end
        else
          begin
            let start = List.length theory.signature.sig_const in
            let cont a =
              if not (seen theory.signature a !unique) then
                unique := (copy_algebra a) :: !unique in
            let rec
                gen_smaller acc = function
                  | k when 2 * k > !size -> acc
                  | k ->
                    begin
                      unique := [] ;
                      Enum.enum k theory cont ;
                      gen_smaller (!unique :: acc) (k+1)
                    end in

            (* There are no algebras with strictly less elements than there are constants. *)
            let unique_by_size = List.rev (gen_smaller (replicate start []) start) in

            unique := gen_reducible theory.signature !size unique_by_size ;

            let cont a =
              if not (seen theory.signature a !unique) then
                begin
                  incr k;
                  unique := (copy_algebra a) :: !unique ;
                  if not !count_only then
                    Print.algebra names
                      (Util.invert (Util.enum_ops theory.signature.sig_unary))
                      (Util.invert (Util.enum_ops theory.signature.sig_binary))
                      a
                end
            in
            Enum.enum !size theory cont ;
            print_endline ("\nTotal count: " ^ string_of_int !k)
          end
      end
with
    Error.Error (pos, err, msg) -> print_endline (err ^ " error: " ^ msg)

