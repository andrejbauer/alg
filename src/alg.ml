(* The main program. *)

open Config
open Output

module A = Algebra
module CM = Check_model

module IntMap = Util.IntMap ;;

(* Convert a string given via the --size command-line option to a list of sizes. *)
let sizes_of_str str =
  let interval_of_str str =
    try
      let k = String.index str '-' in
      let a = int_of_string (String.sub str 0 k) in
      let b = int_of_string (String.sub str (k+1) (String.length str - k - 1)) in
        if a < 0 || b < 0 then
          Error.usage_error "--size does not accept negative integers"
        else
          Util.enumFromTo a b
    with
      | Not_found -> [int_of_string str]
  in
  let lst = ref [] in
  let k = ref 0 in
    try
      while !k < String.length str do
        let m = (try String.index_from str !k ',' with Not_found -> String.length str) in
          lst := Util.union !lst (interval_of_str (String.sub str !k (m - !k))) ;
          k := m + 1
      done ;
      !lst
    with
      | Failure "int_of_string" ->
        Error.usage_error "--size and --groups accept a comma-separated list of non-negative integers and intervals, e.g., 1,2,5-7,9"
;;


let formats = [
  ("text", Output.Markdown.init);
  ("html", Output.HTML.init);
  ("latex", Output.LaTeX.init);
  ("json", Output.JSON.init);
] ;;

let formats_extension = [
  ("txt", "text");
  ("html", "html");
  ("htm", "html");
  ("tex", "latex");
  ("json", "json");
] ;;

(* Main program starts here. *)
try begin (*A big wrapper for error reporting. *)
  
  (* References that store the command-line options *)
  let config = Config.default in

  (* Command-line axioms. *)
  let cmd_axioms = ref [] in
    
  (* Command-line options and usage *)
  let usage = "Usage: alg --size <i,j-k,m> [options] <theory.th>" in

  let options = Arg.align [
    ("--size",
     Arg.String (fun str -> config.sizes <- List.sort compare (Util.union config.sizes (sizes_of_str str))),
     " Comma-separated list of sizes and size intervals from-to.");
    ("--count",
     Arg.Unit (fun () -> config.count_only <- true),
     " Just count the models, do not print them out.");
    ("--axiom",
     Arg.String (fun str -> cmd_axioms := ("Axiom: " ^ str ^ ".") :: !cmd_axioms),
     " Add an extra axiom to the theory.");
    ("--indecomposable",
     Arg.Unit (fun () -> config.indecomposable_only <- true),
     " Output only indecomposable models.");
    ("--paranoid",
     Arg.Unit (fun () -> config.paranoid <- true),
     " Naively check all axioms and isomorphism before output. Use if you think there is a bug in alg.");
    ("--sat",
     Arg.Unit (fun () -> config.use_sat <- true),
     " Use the satisfiability algorithm.");
    ("--no-products",
     Arg.Unit (fun () -> config.products <- false),
     " Do not generate algebras as products of smaller algebras.");
    ("--format",
     Arg.String (fun str -> config.format <- str),                     
     " Output format, one of: " ^ String.concat ", " (List.map fst formats) ^ ".");
    ("--output",
     Arg.String (fun str -> config.output_filename <- str),
     " Output to the specified file.");
    ("--no-source",
     Arg.Unit (fun () -> config.source <- false),
     " Do not include the theory source in the output.");
    ("--load",
     Arg.String  (fun str -> config.load_file <- str),
     " Loads precomputed theories from file.");
    ("--save",
     Arg.String (fun str -> config.save_file <- str),
     " Saves the computed theories in the file.");
    ("--counter",
     Arg.String (fun str -> config.counter_example_to <- str),
     " Find the smallest counter example (only with groups) to the provided expression.");
    ("--groups",
     Arg.String (fun str -> 
       config.groups <- List.sort compare (Util.union config.sizes (sizes_of_str str))),
     " Comma-separated list of group sizes and size intervals from-to, that you want included.");
    ("--version",
     Arg.Unit (fun () ->
       Printf.printf "Copyright (c) 2011 Ales Bizjak and Andrej Bauer\n" ;
       Printf.printf "This is alg version %s compiled on %s for %s.\n" Version.version Version.date Version.os;
       if Version.version.[String.length Version.version - 1] <> '+'
       then Printf.printf "The source code is at http://hg.andrej.com/alg/rev/%s\n" Version.version;
       exit 0
     ),
     " Print version information and exit.");
  ]
  in

    (* First we process the command line. *)

    (* Parse the arguments. Treat the anonymous arguments as files to be read. *)
    Arg.parse options
      (fun str ->
        match config.input_filename with
          | "" -> config.input_filename <- str
          | _ -> raise (Arg.Bad " only one theory file should be given"))
      usage ;

    if !cmd_axioms <> [] then cmd_axioms := "" :: "# Extra command-line axioms" :: !cmd_axioms ;

    (* Read the input files. *)
    let lines =
      begin match config.input_filename with
        | "" -> Arg.usage options usage; exit 1
        | filename ->
          try Util.read_lines filename
          with Sys_error msg -> Error.runtime_error "could not read %s" msg
      end @ !cmd_axioms
    in

    let lex = Lexing.from_string (String.concat "\n" lines) in

    let {Input.th_name=theory_name; Input.th_entries=raw_theory} =
      begin
        try
          Parser.theory Lexer.token lex
        with
          | Parser.Error ->
            Error.syntax_error ~loc:(Common.position_of_lex lex) "I got confused here"
          | Failure "lexing: empty token" ->
            Error.syntax_error ~loc:(Common.position_of_lex lex) "Unrecognized symbol."
      end
    in

    (* Compute the theory name from the file name, if needed. *)
    let theory_name =
      begin match theory_name with
        | Some n -> n
        | None ->
          begin
            let n = Filename.basename config.input_filename in
              try String.sub n 0 (String.index n '.') with Not_found -> n
          end
      end ^ (if !cmd_axioms = [] then "" else "_with_extras")
    in

    (* Parse the theory. *)
    let theory = Cook.cook_theory theory_name raw_theory in

    let theory_with_relations = Array.length theory.Theory.th_predicates > 0 || Array.length theory.Theory.th_relations > 0 in

    (* Configure the output formatter. *)
    if config.format = "" then
      config.format <-
        begin
          try List.assoc (Util.filename_extension config.output_filename) formats_extension
          with Not_found -> fst (List.hd formats)
        end ;
      
      let outch =
        begin
          match config.output_filename with
            | "" -> stdout
            | filename -> open_out filename
        end
      in
        
      let out = 
        begin
          try List.assoc config.format formats config outch lines theory
          with Not_found ->
            Error.runtime_error "unknown output format, should be one of: %s" (String.concat ", " (List.map fst formats))
        end
      in
          
    (* Load precomputed stuff. *)

    (*Read the precomputed theories.??? If possible: make it so, that it only reads if argument present*)
    let preloaded  =
      begin match config.load_file with
        | "" -> ([] : ((int * Algebra.algebra) list))
        | filename -> 
          try 
            let ic = open_in_bin filename in 
            let sth = (Marshal.from_channel ic : ((int * Algebra.algebra) list)) in
            close_in ic ;
            sth
          with Sys_error msg -> Error.runtime_error "could not read %s" msg
      end
    in

    let loaded_groups = Loading_saving_groups.read config.groups (fun msg -> raise (Loading_saving_groups.No_file msg)) in

    let precomputed = Util.union preloaded loaded_groups in
    
    let loaded = IntMap.empty in
    
    let rec fill_in loaded precomputed =
      match precomputed with
        | [] -> loaded
        | (n,a) :: x -> 
          let loaded = IntMap.add n (a :: 
            (try
              (IntMap.find n loaded)
            with Not_found -> [])
          ) loaded in
          fill_in loaded x
    in
    
    let loaded = fill_in loaded precomputed in 
    
    let save_theories = ref [] in
    
    if (config.counter_example_to <> "") then
      let lexx = Lexing.from_string config.counter_example_to in
      let {Input.th_name=theory_name1; Input.th_entries=raw_theory1} =
        begin
          try
            Parser.theory Lexer.token lexx
          with
            | Parser.Error ->
              Error.syntax_error ~loc:(Common.position_of_lex lexx) "I got confused here"
            | Failure "lexing: empty token" ->
              Error.syntax_error ~loc:(Common.position_of_lex lexx) "Unrecognized symbol."
        end
      in
      let theory1 = Cook.cook_theory "" raw_theory1 in
      print_endline "Looking for counterexample.";

      let axs = match theory1.th_axioms with
        | h :: _ -> h
        | _ -> ([||], Theory.True)  (*This should never happen.*)
      in 
      let rec chck lst size axs =
        match lst with
          | [] -> (false, Algebra.empty size theory)
          | h :: hs ->
            if not (First_order.check_formula (snd h) axs) then
               (true, snd h)
            else 
              chck hs size axs
      in
      let rec find_counter size axs =
        match chck (Loading_saving_groups.read [size] (fun msg -> raise (Loading_saving_groups.No_file msg))) size axs with
          | (false, _) -> find_counter (size + 1) axs
          | (true, a) -> a
      in
      try 
        let a = find_counter 1 axs in
        print_endline ("# The counterexample to \""^ config.counter_example_to ^"\" is : \n")    
        (*output (a, true); How to output only this algebra?*)
      with Loading_saving_groups.No_file msg ->
        print_endline ("We ran out of groups to test. Axiom is consistent with all provided groups.")
    ;    
      
      
    (* If --indecomposable is given then --no-products makes no sense. *)
    if config.indecomposable_only then config.products <- true ;

    (* If there are predicates or relations --no-products makes no sense (and will crash). *)
    if theory_with_relations then config.products <- false ;

    (* Cache for indecomposable algebras computed so far. This is a map from size to a list of algebras. *)
    let indecomposable_algebras = ref IntMap.empty in

    let lookup_cached n =
      try
        Some (IntMap.find n !indecomposable_algebras)
      with Not_found -> None
    in

    (* Processing of algebras of a given size and pass them to the given continuations,
       together with information whether the algebra is indecomposable. *)
    let rec process_size n output = begin
      (* Generate a hash table of decomposable algebras if needed. *)
      let (decomposables, save_theories) = 
        if n < Array.length theory.Theory.th_const || not config.products then (Iso.empty_store (),ref [])
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
                        process_size k (fun (algebra, indecomposable) -> 
                        if indecomposable then lst := Util.copy_algebra algebra :: !lst) ;
                        !lst
                  end
                in
                  IntMap.add k lst m)
              IntMap.empty
              (Util.divisors n)
          in
            begin
              (* make (or load) decomposables *)
              Indecomposable.gen_decomposable theory n factors loaded save_theories (fun a -> output (a, false))
            end
      in
      (* Generate indecomposable algebras. *)
      (* Are we going to cache these? *)
      let must_cache = config.products && List.exists (fun m -> n > 0 && m > n && m mod n = 0) config.sizes in
      let algebras = decomposables in
      let to_cache = ref [] in

      let sth = (fun a -> 
        (* XXX check to see if it is faster to call First_order.check_axioms first and then Iso.seen. *)
        let ac = A.make_cache a in
        let aa = A.with_cache ~cache:ac a in
        let (seen, i) = Iso.seen theory aa algebras in
          if not seen && First_order.check_axioms theory a then
            if config.paranoid && CM.seen theory a algebras then
              Error.internal_error "There is a bug in isomorphism detection in alg.\nPlease report with example."
            else
              begin
                let b = Util.copy_algebra a in
                let bc = A.with_cache ~cache:ac b in
                  Iso.store algebras ~inv:i bc ;
                  if must_cache then to_cache := b :: !to_cache ;
                  save_theories := (b.alg_size, b) :: !save_theories ; (*Here b can be of wrong size.*)
                  output (b, true)
              end)
      in
      try 
        let lst = IntMap.find n loaded in
        (List.iter sth lst) ;
      with Not_found -> 
        ((if config.use_sat then Sat.generate ?start:None else Enum.enum) n theory sth);
      if must_cache then indecomposable_algebras := IntMap.add n !to_cache !indecomposable_algebras
    end (* process_size *)

    in

      let counts = ref [] in
      let counts = ref [] in
        
      (* The main loop *)
      begin
        Sys.catch_break true ;
        out.header () ;
        if config.count_only then out.count_header () ;
        begin 
          try
            let sth = List.iter
              (fun n -> 
                if not config.count_only then out.size_header n ;
                let k = ref 0 in
                let output (algebra, indecomposable) =
                  if config.paranoid && not (CM.check_model theory algebra) then
                    Error.internal_error "There is a bug in alg. Algebra does not satisfy all axioms.\nPlease report with example." ;
                  if not config.indecomposable_only || indecomposable then incr k ;
                  algebra.Algebra.alg_name <- Some (theory.Theory.th_name ^ "_" ^ string_of_int n ^ "_" ^ string_of_int !k) ;
                  if not config.count_only && (not config.indecomposable_only || indecomposable)
                  then out.algebra algebra 
                in
                  process_size n output ;
                  counts := (n, !k) :: !counts ;
                  if config.count_only
                  then out.count n !k
                  else out.size_footer ()
              )
              config.sizes
            in
            begin match config.save_file with
              | "" -> ()
              | filename -> 
                try 
                  let oc = open_out_bin filename in
                    Marshal.to_channel oc (!save_theories : ((int * Algebra.algebra) list)) [] ;
                    close_out oc ;
                with Sys_error msg -> Error.runtime_error "could not write to %s" msg
            end ;
            sth
          with Sys.Break -> out.interrupted ()
        end ;
        if config.count_only
        then out.count_footer (List.rev !counts)
        else out.footer (List.rev !counts)
      end
end
with Error.Error err -> Print.error err
