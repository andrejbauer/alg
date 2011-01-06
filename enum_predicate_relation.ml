open Theory
open Algebra

(* Check if all of the axioms are still valid and fill 
   predicates or relations where possible. 
   Returns pair (b, undos) where b is true if no contradiction
   was encountered (this does not mean there is no contradiction)
   and false otherwise. undos is a list of actions needed
   to return predicates and relations to previous state.
*)
let check_and_fill axioms ({alg_const=c;
                            alg_unary=u;
                            alg_binary=b;
                            alg_predicates=p;
                            alg_relations=r;
                            alg_size=n} as alg) = 
  let rec eval_fill vars undos target = function 
    | True -> (target, undos)
    | False -> (not target, undos)
    | Equal (t1,t2) -> (true, undos)
    | Forall (v, f) when target -> 
      let rec eval_forall undos = function
        | i when i = n -> (true, undos)
        | i -> begin
          vars.(v) <- i;
          let (t,unds) = eval_fill vars undos true f in
          if not t then (false, unds) else eval_forall unds (i+1)
        end in
      eval_forall undos 0 (* TODO: should probably set vars.(v) back to -1 *)
    | Forall (v,f) -> (true, undos)
    | Exists (v,f) when target -> (true, undos)
    | Exists (v,f) -> eval_fill vars undos true (Forall (v,f))
    | And (f1,f2) when target -> 
      let (t,unds) = eval_fill vars undos true f1 in
      if not t then (false, unds) else eval_fill vars unds true f2
    | And (f1,f2) -> 
      let t1 = Eval.eval_formula alg vars f1 in
      let t2 = Eval.eval_formula alg vars f2 in
      begin
        match t1,t2 with
          | (Some true, Some true) -> (false, undos)
          | (Some true, None) -> eval_fill vars undos false f2
          | (None, Some true) -> eval_fill vars undos false f1
          | _ -> (true, undos)
      end
    | Or (f1,f2) when target -> 
      let t1 = Eval.eval_formula alg vars f1 in
      let t2 = Eval.eval_formula alg vars f2 in
      begin
        match t1,t2 with
          | (Some false, Some false) -> (false, undos)
          | (Some false, None) -> eval_fill vars undos true f2
          | (None, Some false) -> eval_fill vars undos true f1
          | _ -> (true, undos)
      end
    | Or (f1,f2) -> eval_fill vars undos true (And (f1,f2))
    | Imply (f1,f2) when target -> 
      let t1 = Eval.eval_formula alg vars f1 in
      let t2 = Eval.eval_formula alg vars f2 in
      begin
        match t1,t2 with
          | (Some true, Some false) -> (false, undos)
          | (Some true, None) -> eval_fill vars undos true f2
          | (None, Some false) -> eval_fill vars undos false f1
          | _ -> (true, undos)
      end
    | Imply (f1,f2) -> 
      let (t,unds) = eval_fill vars undos true f1 in
      if not t then (false, unds) else eval_fill vars unds false f2
    | Iff (f1,f2) when target -> 
      let t1 = Eval.eval_formula alg vars f1 in
      let t2 = Eval.eval_formula alg vars f2 in
      begin
        match t1,t2 with
          | (Some true, Some false) 
          | (Some false, Some true) -> (false, undos)
          | (Some t, None) -> eval_fill vars undos t f2
          | (None, Some t) -> eval_fill vars undos t f1
          | _ -> (true, undos)
      end
    | Iff (f1,f2) -> 
      let t1 = Eval.eval_formula alg vars f1 in
      let t2 = Eval.eval_formula alg vars f2 in
      begin
        match t1,t2 with
          | (Some true, Some true) 
          | (Some false, Some false) -> (false, undos)
          | (Some t, None) -> eval_fill vars undos (not t) f2
          | (None, Some t) -> eval_fill vars undos (not t) f1
          | _ -> (true, undos)
      end
    | Not f -> eval_fill vars undos (not target) f
    | Predicate (i, t) -> begin
      match Eval.eval_term_partial alg vars t with
        | None -> (true,undos)
        | Some r -> 
          if p.(i).(r) = -1 then 
            begin
              p.(i).(r) <- if target then 1 else 0;
              (true, (0, (i,r,-1))::undos)
            end
          else (p.(i).(r) = (if target then 1 else 0), undos)
    end
    | Relation (i, t1,t2) -> 
      let r1 = Eval.eval_term_partial alg vars t1 in
      let r2 = Eval.eval_term_partial alg vars t2 in
      match r1,r2 with
        | Some r1, Some r2 -> 
          if r.(i).(r1).(r2) = -1 then 
            begin
              r.(i).(r1).(r2) <- if target then 1 else 0;
              (true, (1, (i,r1,r2))::undos)
            end
          else (r.(i).(r1).(r2) = (if target then 1 else 0), undos)
        | _ -> (true, undos)
  in (* end of eval_fill *)
  let rec for_all_axioms (b, undos) = function
    | [] -> (b,undos)
    | ((vars,f)::fs) -> begin
      match eval_fill vars [] true f with
        | (true, unds) -> for_all_axioms (true, unds @ undos) fs
        | (false, unds) -> (false, unds @ undos)
    end in
  for_all_axioms (true, []) axioms

let undo {alg_predicates=ps; alg_relations=rs} undos =
  let rec undo = function
    | [] -> ()
    | ((0,(p,e,_))::us) -> ps.(p).(e) <- -1 ; undo us
    | ((1,(r,e1,e2))::us) -> rs.(r).(e1).(e2) <- -1 ; undo us
    | _ -> invalid_arg "invalid element in undos"
  in undo undos
 


(* Silly predicate enumeration. *)

let gen_predicate th ({alg_size=n; 
                       alg_predicates=predicate_arr} as alg) cont =
  let lp = Array.length th.th_predicates in
  let rec gen_predicate i = function
    | j when j = n && i < lp - 1 -> gen_predicate (i+1) 0
    | j when j = n || i = lp -> cont ()
    | j when predicate_arr.(i).(j) = -1 ->
      for b = 0 to 1 do
        predicate_arr.(i).(j) <- b ;
        let (p, undos) = check_and_fill th.th_axioms alg in
        if p then gen_predicate i (j+1) ;
        undo alg undos ;
        predicate_arr.(i).(j) <- -1 ;
      done
    | j -> gen_predicate i (j+1)
  in gen_predicate 0 0

(* Silly predicate enumeration. *)

let gen_predicate th ({alg_size=n; 
                       alg_predicates=predicate_arr} as alg) cont =
  let lp = Array.length th.th_predicates in
  let rec gen_predicate i = function
    | j when j = n && i < lp - 1 -> gen_predicate (i+1) 0
    | j when j = n || i = lp -> cont ()
    | j when predicate_arr.(i).(j) = -1 ->
      for b = 0 to 1 do
        predicate_arr.(i).(j) <- b ;
        let (p, undos) = check_and_fill th.th_axioms alg in
        if p then gen_predicate i (j+1) ;
        undo alg undos ;
        predicate_arr.(i).(j) <- -1 ;
      done
    | j -> gen_predicate i (j+1)
  in gen_predicate 0 0

let gen_relation th ({alg_size=n; 
                      alg_relations=relation_arr} as alg) cont =
  let lr = Array.length th.th_relations in
  let rec gen_relation r = function
    | _ when r = lr -> cont ()
    | (i,_) when i = n -> gen_relation (r+1) (0,0)
    | (i,j) when j = n -> gen_relation r (i+1,0)
    | (i,j) when relation_arr.(r).(i).(j) = -1 ->
      for b=0 to 1 do
        relation_arr.(r).(i).(j) <- b ;
        let (p, undos) = check_and_fill th.th_axioms alg in
        if p then gen_relation r (i,j+1) ;
        undo alg undos ;
        relation_arr.(r).(i).(j) <- -1
      done
    | (i,j) ->  gen_relation r (i,j+1) in
  gen_relation 0 (0,0)
