(* The main program. *)

open Type

module AlgSet =
  Set.Make(struct
    type t = int
    let compare = compare
  end)

(* A big wrapper for error reporting. *)
  try begin

    (* References that store the command-line options *)
    let size = ref [] in
    let indecomposable = ref false in
    let count_only = ref false in
    let input_filename = ref None in
    let products = ref true in

    (* Command-line options and usage *)
    let usage = "Usage: alg --size <n> <theory.th>" in

    let options = Arg.align [
      ("--help",
       Arg.Unit (fun () -> print_endline usage; exit 0),
       " Print this jelp");
      ("--size",
       Arg.String (fun str -> size := List.sort compare (Util.union !size (Util.sizes_of_str str))),
       " Comma-separated list of sizes and size intervals m-n that should be considered.");
      ("--count",
       Arg.Set count_only,
       " Just count the models, do not print them out.");
      ("--indecomposable",
       Arg.Set indecomposable,
       " Output only indecomposable models.");
      ("--no-products",
       Arg.Unset products,
       " Do not try to generate algebras as products of smaller algebras.");
    ]
    in

    (* First we process the command line. *)

    (* Parse the arguments. Treat the anonymous arguments as files to be read. *)
    Arg.parse options
      (fun str ->
        match !file with
          | None -> file := Some str
          | Some _ -> raise (Arg.Bad " only one theory file should be given"))
      usage ;

    (* Read the input file. *)
    let file_name, fh =
      begin match !file with
        | None -> Error.fatal "please provide a theory file on the command line"
        | Some f -> f, open_in f
      end
    in

    let lex = Lexing.from_channel fh in

    let theory_name, raw_theory =
      begin
        try
          Parser.theory Lexer.token lex
        with
          | Parser.Error ->
            Error.syntax ~pos:(Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex) ""
          | Failure "lexing: empty token" ->
            Error.syntax ~pos:(Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex) "Unrecognised symbol."
      end
    in

    close_in fh ;

    let theory_name =
      begin match theory_name with
        | Some n -> n
        | None ->
          begin
            let n = Filename.basename file_name in
            try String.sub n 0 (String.index n '.') with Not_found -> n
          end
      end

      (* Parse the theory. *)
      let theory = Cook.cook_theory theory_name raw_theory in

      (* The algebras that are needed for computation of other, larger algebras. *)
      let algebras = ref AlgSet.empty in

      (* Processing of algebras of a given size. Each algebra found is passed to the given continuation. 
         Return the total number of algebras found. *)
      let process_size n kont = 
        if n < Array.length theory.th_const
        then 0
        else begin
          let count = ref 0 in

          if not !indecomposable then
          begin
            let cont a =
              if not (Iso.seen theory a !unique) && First_order.check_axioms theory a then
                begin
                  incr k;
                  unique := (Util.copy_algebra a) :: !unique ;
                  if not !count_only then
                    Print.algebra names !k theory a
                end
            in
              Enum.enum n theory cont ;
              Printf.printf "The number of models of theory %s of size %d is %d.\n" theory.th_name !size !k
          end
        else (* Indecomposable only. *)
          (* TODO: We don't necessarily have products. *)
          begin
            let indecomposable = ref 0 in
            let start = Array.length theory.th_const in
            let cont a =
              if not (Iso.seen theory a !unique) && First_order.check_axioms theory a then
                begin
                  let a' = Util.copy_algebra a in
                  unique := a' :: !unique ;
                  incr indecomposable
                end in
            let rec
                gen_smaller acc = function
                  | k when 2 * k > !size -> acc
                  | k ->
                    begin
                      unique := Indecomposable.gen_decomposable theory k acc ;
                      indecomposable := 0 ;
                      Enum.enum k theory cont ;
                      gen_smaller (Util.rev_take !indecomposable !unique :: acc) (k+1)
                    end in

            (* There are no algebras with strictly fewer elements than there are constants. *)
            let indecomposable_by_size = List.rev (gen_smaller (Util.replicate start []) start) in

            unique := Indecomposable.gen_decomposable theory !size indecomposable_by_size ;

            let cont a =
              if not (Iso.seen theory a !unique) && First_order.check_axioms theory a then
                begin
                  incr k;
                  unique := (Util.copy_algebra a) :: !unique ;
                  if not !count_only then
                    Print.algebra names !k theory a
                end
            in
              Enum.enum !size theory cont ;
              Printf.printf "The number of models of theory %s of size %d is %d.\n" theory.th_name !size !k
          end
      end
      in

      let k = ref 0 in

      let unique = ref [] in
      
      List.iter process_size !size
with
    e as Error.error -> Error.report err
      Format.eprintf "%s error: %s %t@." err msg (Error.position pos); exit 1
