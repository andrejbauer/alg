(* The main program. *)

open Type

module IntMap = Util.IntMap ;;

(* A big wrapper for error reporting. *)
  try begin

    (* References that store the command-line options *)
    let sizes = ref [] in
    let indecomposable_only = ref false in
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
       Arg.String (fun str -> sizes := List.sort compare (Util.union !sizes (Util.sizes_of_str str))),
       " Comma-separated list of sizes and size intervals m-n that should be considered.");
      ("--count",
       Arg.Set count_only,
       " Just count the models, do not print them out.");
      ("--indecomposable",
       Arg.Set indecomposable_only,
       " Output only indecomposable models.");
      ("--no-products",
       Arg.Clear products,
       " Do not try to generate algebras as products of smaller algebras.");
    ]
    in

    (* First we process the command line. *)

    (* Parse the arguments. Treat the anonymous arguments as files to be read. *)
    Arg.parse options
      (fun str ->
        match !input_filename with
          | None -> input_filename := Some str
          | Some _ -> raise (Arg.Bad " only one theory file should be given"))
      usage ;

    (* Read the input file. *)
    let file_name, fh =
      begin match !input_filename with
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

    (* Compute the theory name from the file name, if needed. *)
    let theory_name =
      begin match theory_name with
        | Some n -> n
        | None ->
          begin
            let n = Filename.basename file_name in
            try String.sub n 0 (String.index n '.') with Not_found -> n
          end
      end in

    (* Parse the theory. *)
    let theory = Cook.cook_theory theory_name raw_theory in
      
    (* If --indecomposable is given then --no-products makes no sense. *)
    if !indecomposable_only then products := true ;

    (* Cache storing indecomposable algebras computed so far. *)
    let indecomposable_algebras = ref IntMap.empty in

    let lookup_cached n =
      try
        Some (IntMap.find n !indecomposable_algebras)
      with Not_found -> None
    in

    (* Processing of algebras of a given size and pass them to the given continuations,
       together with information whether the algebra is indecomposable. *)
    let rec process_size n output =
      (* Generate decomposable algebras if needed. *)
      let decomposables = 
        if n < Array.length theory.th_const || not !products then []
        else
          (* Generate indecomposable factors and then decomposable algebras from them. *)
          let factors =
            List.fold_left
              (fun m k ->
                 let lst =
                   begin match lookup_cached k with
                     | Some lst -> lst
                     | None ->
                         let lst = ref [] in
                           process_size k (fun (algebra, indecomposable) -> if indecomposable then lst := algebra :: !lst) ;
                           !lst
                   end
                 in
                   IntMap.add k lst m)
              IntMap.empty
              (Util.divisors n)
          in
            begin
              (* make decomposables *)
              Indecomposable.gen_decomposable theory n factors (fun a -> output (a, false))
            end
      in
      (* Generate indecomposable algebras. *)
      (* Are we going to cache these? *)
      let must_cache = !products && List.exists (fun m -> n > 0 && m > n && m mod n = 0) !sizes in
      let algebras = ref decomposables in
      let to_cache = ref [] in
        Enum.enum n theory
          (fun a -> 
             if First_order.check_axioms theory a && not (Iso.seen theory a !algebras) then
               begin
                 algebras := Util.copy_algebra a :: !algebras ;
                 if must_cache then to_cache := a :: !to_cache ;
                 output (a, true)
               end) ;
        if must_cache then indecomposable_algebras := IntMap.add n !to_cache !indecomposable_algebras
    in

    (* The main loop *)
    begin
      List.iter
        (fun n -> 
           let k = ref 0 in
           let names = Print.names n theory in
           let output (algebra, indecomposable) =
             incr k ;
             if not !count_only && (not !indecomposable_only || indecomposable)
             then Print.algebra names !k theory algebra
           in
             process_size n output ;
             Printf.printf "The number of models of theory %s of size %d is %d.\n%!" theory.th_name n !k)
        !sizes
    end
  end
  with Error.Error (pos, err, msg) -> Error.report (pos, err, msg)

(*
(* GARBAGE        -------------------------------------------- *)
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
*)
