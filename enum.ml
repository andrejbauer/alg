open Type
open Util

(* TODO This module is a little messy. *)

(* Select axioms that refer only to unary operations and constants. *)
let part_axioms axioms =
  let rec no_binary = function
    | Binary _ -> false
    | Unary (_, t) -> no_binary t
    | Var _ | Const _ -> true in
  let no_binary_axiom (eq1, eq2) = no_binary eq1 && no_binary eq2 in
  List.partition no_binary_axiom axioms


(*
   Partition unary axioms. In the first part are the axioms of the form
   f(a) = b, where a and b are constants, and the rest in the second one.
*)
let part_unary_axioms axioms =
  let is_simple = function
    | (Unary (_,Const _), Const _)
    | (Const _, Unary (_,Const _)) -> true
    | _ -> false
  in List.partition is_simple axioms

(*
   Partition binary axioms into two parts. In the first are axioms of the form
   a + b = c, where a b and c are constants or unary applications, these are termed simple,
   and the rest are in the second part, these I call complicated.
*)
let part_binary_axioms axioms =
  let rec const_and_unary = function
    | (Unary (_,t)) -> const_and_unary t
    | (Const _ ) -> true
    | _ -> false in
  let is_simple = function
    | (Binary (_,t1,t2), Const _)
    | (Const _, Binary (_,t1,t2)) -> const_and_unary t1 && const_and_unary t2
    | _ -> false
  in List.partition is_simple axioms

(*
  Partition binary axioms into two parts.
  The first:
     axioms f(a) * g(a) = h(a) or some of the expressions contain a constant
  The second:
     all the rest. :)
  We can immediately apply the first kind.
*)

let part_one_var_binary axioms =
  let rec const_var_unary = function
    | (Unary (_,t)) -> const_var_unary t
    | (Const c ) -> Some (Const c)
    | (Var v) -> Some (Var v)
    | _ -> None in
  let is_simple = function
    | (Binary (_,t1,t2), t3)
    | (t3, Binary (_,t1,t2)) ->
      let v1 = const_var_unary t1 in
      let v2 = const_var_unary t2 in
      let v3 = const_var_unary t3 in
      begin
        match (v1,v2,v3) with
          (* This could be more easily done with a list *)
          | (Some (Const _), Some (Const _), Some (Const _))
          | (Some (Var _), Some (Const _), Some (Const _))
          | (Some (Const _), Some (Var _), Some (Const _))
          | (Some (Const _), Some (Const _), Some (Var _)) -> true
          | (Some (Var v1), Some (Var v2), Some (Const _))
          | (Some (Var v1), Some (Const _), Some (Var v2))
          | (Some (Const _), Some (Var v1), Some (Var v2)) -> v1 = v2
          | (Some (Var v1), Some (Var v2), Some (Var v3)) -> v1 = v2 && v2 = v3
          | (None,_,_) | (_,None,_) | (_,_,None) -> false
          | _ -> failwith "Binary operation creeped in part_one_binary.is_simple."
      end
    | _ -> false
  in List.partition is_simple axioms


let make_3d_array x y z initial =
  let base = Array.make x initial in
  Array.map (fun _ -> Array.make_matrix y z initial) base


(*
  Depth of an axiom is maximum of the depths of the equations.
  Depth of an equation is the number of binary operations in it.
*)
let axiom_depth (left, right) =
  let rec term_depth acc = function
    | (Unary (_,t)) -> term_depth acc t
    | (Var _) | (Const _) -> acc
    | (Binary (_,t1,t2)) -> term_depth (term_depth (1+acc) t1) t2
  in max (term_depth 0 left) (term_depth 0 right)

(*
  List of distinct variables of an axiom.
  Obviously quadratic in number of variables. TODO
*)
let dist_vars (left, right) =
  let rec
      eq_vars acc = function
        | Const _ -> acc
        | Var v -> if List.mem v acc then acc else (v :: acc)
        | Binary (_,t1,t2) -> let lv = eq_vars acc t1 in
                              eq_vars lv t2
        | Unary (_,t) -> eq_vars acc t in
  let lv = eq_vars [] left in eq_vars lv right


(*
  Number of distinct variables in an axiom.
*)
let num_dist_vars a = List.length (dist_vars a)


(* ************************************************************************** *)
(* Main search functions. *)

(*
   Generate binary operation tables. const, unary and binary are
   assumed to be assoc lists, unary_arr is supposed to be a matrix
   of unary operations where each line is an operation. axioms
   should only contain axioms where there is at least one binary
   operation.
*)
let gen_binary n const lu lb axioms unary_arr k =
  let (simple, complicated) = part_binary_axioms axioms in

  (*
     Main operation tables.
  *)
  let binary_arr = make_3d_array lb n n (-1) in

  (*
     Applies simple axioms to the main operation tables.
     If axioms aren't simple it fails miserably.
  *)
  let apply_simple axiom =
    let rec get_value = function
      | (Const c) -> c
      | (Unary (op,v)) -> unary_arr.(op).(get_value v)
      | _ -> failwith "Ooops, binary operation or variable in apply_simple.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), Const c)
      | (Const c, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        binary_arr.(op).(v1).(v2) <- c

      | _ -> failwith "Not a simple binary axiom."
  in List.iter apply_simple simple ;

  (*
     left are the axioms which cannot be immediately applied
     These include axioms of depth > 1 and those with more variables.
  *)

  let (one_var_shallow, left) = part_one_var_binary complicated in

  (*
    Apply one variable shallow axioms. Typical example is axioms for
    a unit element in a monoid (forall a: a * e = e)
  *)

  let apply_one_var axiom elem =
    let rec get_value = function
      | (Const c) -> c
      | (Var _) -> elem
      | (Unary (op,v)) -> unary_arr.(op).(get_value v)
      | _ -> failwith "Ooops, binary operation in apply_one_var.get_value. This shouldn't happen!"
    in match axiom with
      | (Binary (op, t1, t2), t3)
      | (t3, Binary (op, t1, t2)) ->
        let v1 = get_value t1 in
        let v2 = get_value t2 in
        let v3 = get_value t3 in
        binary_arr.(op).(v1).(v2) <- v3
      | _ -> failwith "not a legal axiom in apply_one_var"
  in
  for i=0 to n-1 do
    List.iter (fun x -> apply_one_var x i) one_var_shallow
  done ;

  let zipped_axioms = List.map (fun a -> (num_dist_vars a, a)) left in
  let max_vars = List.fold_left max 0 (List.map num_dist_vars left) in 

  (* This could potentially gobble up memory. TODO *)
  let all_tuples = 
    let arr = Array.make (max_vars + 1) 0 in
    Array.mapi (fun i _ -> ntuples n i) arr in

  (*
     Returns false if there is a conflict.
  *)
  let axiom_ok (num_vars, (left, right)) =

    let tuples = all_tuples.(num_vars) in
    let rec eval_eq i = function
      | (Const c) -> Some c
      | (Var v) -> Some (i.(v))
      | (Unary (op, t)) ->
        begin
          match eval_eq i t with
            | None -> None
            | Some v when v = -1 -> None
            | Some v -> Some unary_arr.(op).(v)
        end
      | (Binary (op, lt, rt)) ->
        begin
          (* This would be faster if I first checked the left side
             and then the right only if left is not None *)
          match (eval_eq i lt, eval_eq i rt) with
            | (None, _) | (_, None) -> None
            | (Some lv, Some rv) when lv = -1 || rv = -1 -> None
            | (Some lv, Some rv) -> let r = binary_arr.(op).(lv).(rv) in
                                    if r = -1 then None else (Some r)
        end in
    let apply_to i =
      match (eval_eq i left, eval_eq i right) with
        | (None,_) | (_,None) -> true
        | (Some v1, Some v2) -> v1 = v2 in
    Array.fold_left (fun acc c -> acc && apply_to c) true tuples in


  (*
    Checks if all axioms are still valid.
    TODO: Needlessly slow.
  *)
  let check () = List.for_all axiom_ok zipped_axioms in


  (* Main loop. *)
  (* o is index of operation, (i,j) current element *)
  let rec gen_operation o = function
    | _ when o = lb ->
      k { size = n;
          const = const;
          unary =
          begin
            let r = ref [] in
            for i=0 to lu - 1 do
              r := (i, unary_arr.(i)) :: !r
            done ; !r
          end ;
          binary = let r = ref [] in
                   for i=0 to lb-1 do
                     r := (i, binary_arr.(i)) :: !r
                  done ; !r
        }
    | (i,_) when i = n -> gen_operation (o+1) (0,0)
    | (i,j) when j = n -> gen_operation o (i+1,0)
    | (i,j) when binary_arr.(o).(i).(j) = -1 ->
      for k=0 to n-1 do
        binary_arr.(o).(i).(j) <- k ;
        if check () then
          gen_operation o (i,j+1)
        else () ;
        binary_arr.(o).(i).(j) <- -1 ;
      done
    | (i,j) ->  gen_operation o (i,j+1) in
  gen_operation 0 (0,0)


(*
   I'm assuming that unary operations are bijections. This should
   probably be changed. TODO
   const, unary and binary are assumed to be a assoc lists
*)
let gen_unary n const lu lb axioms k =
  let (unary_axioms, binary_axioms) = part_axioms axioms in
  (*
     Simple and complicated unary axioms. Simple are the
     ones of the form f(c) = d or f(d) = c for c and d constants. These
     can be easily applied.
     TODO: Axioms of the form f(x) = c for x variable and c constant
     and f(c) = x are also easily dispatched with.

     Complicated are the complement of simple and cannot be so easily applied.
     TODO: The ones of the form f_1(...(f_n(c))) = d for c and d constants create
     connections between tables. If c and d are variables this is the same as
     n^2 pairs of constant.
  *)
  let (simple, complicated) = part_unary_axioms unary_axioms in
  (*
     Preliminary version. Equation consists only of unary operations and variables.
     TODO: If we don't require bijections then f_1(...f_n(x)...) = c are also valid.
  *)
  let path_from_equation e =
    let rec loop acc = function
      | (Unary (op,t)) -> loop (op::acc) t
      | (Var v) -> v :: acc
      (* | (Const c) -> c :: acc *)
      | _ -> failwith "path_from_equation: Not yet implemented."
    in loop [] e in

  let paths_from_axioms = List.map (function
    | (eq1, eq2) -> (path_from_equation eq1, path_from_equation eq2)) complicated in

  (* If there is a different variable on the left and right side of the equation,
     then there is at least one unary operation, that cannot possibly be a bijection.
     TODO: constants and axioms of the form forall a,b f_1(...(f_n(a))...) = b
  *)
  let normal_axioms = List.map (function
    | (eq1, eq2) -> (List.tl eq1, List.tl eq2))
    (List.filter (function | (eq1, eq2) -> (List.hd eq1 = List.hd eq2)) paths_from_axioms) in

  (* Main operation tables *)
  let unary_arr = Array.make_matrix lu n (-1) in

  (* Apply simple axioms *)
  List.iter
    (function
      | (Unary (op, Const c1), Const c2)
      | (Const c2, Unary (op, Const c1))
        -> unary_arr.(op).(c1) <- c2
      | _ -> failwith "Something went terribly wrong!")
    simple ;

  (*
     Returns false if there is a conflict with the axiom a, starting with element start.
     Axiom is assumed to be in "normal form" (list of applications).

     This can be improved. For example in a situation where we get to the situation
     where f(c) = d we can set f(c) immediately.
  *)
  let axiom_ok start a =
    (* Not using foldleft because I possibly need to short circuit. *)
    let rec result acc = function
      | [] -> Some acc
      | (x::xs) ->  let r = unary_arr.(x).(acc) in
                   if r = -1 then None else result r xs in
    match (result start (fst a), result start (snd a)) with
      | (Some r1, Some r2) -> r1 = r2
      | _ -> true in
  (*
     Global array of already taken symbols. If we don't require bijections
     then this is useless. It is initialized with with values from simple axioms.
  *)
  let taken =
    let used = Array.make_matrix lu n false in
    for i=0 to lu-1 do
      for k=0 to n-1 do
        used.(i).(k) <- unary_arr.(i).(k) != -1
      done
    done ; used in

  (* Check if any of the equations are broken by starting with
     every element and tracing function applications.
  *)
  let check () =
    let p = ref true in
    for k=0 to n-1 do
      p := !p && List.for_all (axiom_ok k) normal_axioms
    done ; !p in

  (*
     Main loop. Baseline.
  *)
  let rec
      gen_operation i = function
        | j when j = n && i < lu - 1 -> gen_operation (i+1) 0
        | j when j = n || i = lu -> gen_binary n const lu lb binary_axioms unary_arr k
          (* || i = lu is necessary for when there aren't any unary operations *)
        | j when unary_arr.(i).(j) = -1 ->
          for k=0 to n-1 do
            if not taken.(i).(k) then
              (unary_arr.(i).(j) <- k ; taken.(i).(k) <- true ;
               if check () then
                   gen_operation i (j+1)
               else () ;
               unary_arr.(i).(j) <- -1 ; taken.(i).(k) <- false)
            else ()
          done
        | j -> gen_operation i (j+1)
  in gen_operation 0 0


(*
   Enumerate all algebras of a given size for the given theory
   and pass them to the given continuation.
*)
let enum n {signature={sig_const=const; sig_unary=unary; sig_binary=binary}; axioms=axioms} k =
  gen_unary n (enum_ops const) (List.length unary) (List.length binary) axioms k
