(* An alternative algorithm for generation of algebras that uses the following
   strategy.

   Given a partially created algebra, i.e., with some -1's in some places, we
   check axioms. Checking an axiom may lead to one of the following results:

   - an axiom is invalid, in which case we must backtrack

   - an axiom is valid, we continue

   - an axiom can be made valid in one of several ways, in which
     case we branch on them.
*)

open Theory
open Algebra

type partial_term =
  | TValue of int
  | TPartial of term * int

type partial_formula =
  | FValue of bool
  | FPartial of formula' * int

let print_conjuncts cs =
  Printf.printf "conjuncts (%d):\n%s\n"
    (List.length cs)
    (String.concat "\n" (List.map (function
                                     | FValue b -> string_of_bool b
                                     | FPartial (f, k) -> string_of_int k ^ " ... " ^ string_of_formula' f) cs))

let compare_partial_formulas f1 f2 =
  match f1, f2 with
    | FValue b, FValue b' -> compare b b'
    | FValue _, _ -> -1
    | _, FValue _ -> 1
    | FPartial (_, k1), FPartial (_, k2) -> k1 - k2

exception Result of bool

let and_of n i f =
  let rec loop k a =
    if k = n
    then a
    else loop (k+1) (And (subst_formula i (Elem k) f, a))
  in
    if n = 0 then True else loop 1 (subst_formula i (Elem 0) f)

let or_of n i f =
  let rec loop k a =
    if k = n
    then a
    else loop (k+1) (Or (subst_formula i (Elem k) f, a))
  in
    if n = 0 then True else loop 1 (subst_formula i (Elem 0) f)

(* Generate all algebras for theory [th] of size [n]. Pass each one to the
   continuation [k]. *)
let generate n ({th_const=const; th_equations=eqs; th_axioms=axs} as th) k =
  if n >= Array.length const then begin
    let a = Algebra.empty n th in
    let const = a.alg_const in
    let unary = a.alg_unary in
    let binary = a.alg_binary in
    let pred = a.alg_predicates in
    let rel = a.alg_relations in

    (* Partial evlauation of a term. It returns the partially evaluated term together
       with a count of how many table entries need to be filled in for the term to 
       become completely evaluated. *)
    let rec eval_term = function
      | Var i -> Error.fatal "eval_term: variable encountered"
      | Elem e -> TValue e
      | Const i -> TValue const.(i) (* NB: We assume constants are always defined. *)
      | Unary (op, t) ->
          begin match eval_term t with
            | TValue v ->
                if unary.(op).(v) = -1
                then TPartial (Unary(op, Elem v), 1)
                else TValue unary.(op).(v)
            | TPartial (t, k) -> TPartial (Unary (op, t), k+1)
          end
      | Binary (op, t1, t2) ->
          begin match eval_term t1, eval_term t2 with
            | TValue v1, TValue v2 ->
                let u = binary.(op).(v1).(v2) in
                  if u = -1
                  then TPartial (Binary (op, Elem v1, Elem v2), 1)
                  else TValue u
            | TValue v1, TPartial (t2,k2) -> TPartial (Binary (op, Elem v1, t2), k2+1)
            | TPartial (t1,k1), TValue v2 -> TPartial (Binary (op, t1, Elem v2), k1+1)
            | TPartial (t1,k1), TPartial (t2,k2) -> TPartial (Binary (op, t1, t2), k1+k2+1)
          end
    in

    let rec eval_formula = function
      | True -> FValue true
      | False -> FValue false
      | Predicate (p, t) ->
          begin match eval_term t with
            | TValue v ->
                let u = pred.(p).(v) in
                  if u = -1
                  then FPartial (Predicate (p, Elem v), 1)
                  else FValue (u = 1)
            | TPartial (t, k) -> FPartial (Predicate (p, t), k+1)
          end
      | Relation (r, t1, t2) ->
          begin match eval_term t1, eval_term t2 with
            | TValue v1, TValue v2 ->
                let u = rel.(r).(v1).(v2) in
                  if u = -1
                  then FPartial (Relation (r, Elem v1, Elem v2), 1)
                  else FValue (u = 1)
            | TValue v1, TPartial (t2,k2) -> FPartial (Relation (r, Elem v1, t2), k2+1)
            | TPartial (t1,k1), TValue v2 -> FPartial (Relation (r, t1, Elem v2), k1+1)
            | TPartial (t1,k1), TPartial (t2,k2) -> FPartial (Relation (r, t1, t2), k1+k2+1)
          end
      | Equal (t1, t2) ->
          begin match eval_term t1, eval_term t2 with
            | TValue v1, TValue v2 -> FValue (v1 = v2)
            | TValue v1, TPartial (t2,k2) -> FPartial (Equal (Elem v1, t2), k2)
            | TPartial (t1,k1), TValue v2 -> FPartial (Equal (Elem v2, t1), k1)
            | TPartial (t1,k1), TPartial (t2,k2) ->
                if k1 < k2
                then FPartial (Equal(t1, t2), k1+k2)
                else FPartial (Equal(t2, t1), k1+k2)
          end
      | Not f ->
          begin match eval_formula f with
            | FValue b -> FValue (not b)
            | FPartial (f,k) -> FPartial (Not f, k)
          end
      | And (f1, f2) ->
          begin match eval_formula f1 with
            | FValue true -> eval_formula f2
            | FValue false -> FValue false
            | FPartial (f1,k1) ->
                begin match eval_formula f2 with
                  | FValue true -> FPartial (f1,k1)
                  | FValue false -> FValue false
                  | FPartial (f2,k2) ->
                      if k1 < k2
                      then FPartial (And (f1,f2), k1+k2)
                      else FPartial (And (f2,f1), k1+k2)
                end
          end
      | Or (f1, f2) ->
          begin match eval_formula f1 with
            | FValue false -> eval_formula f2
            | FValue true -> FValue true
            | FPartial (f1,k1) ->
                begin match eval_formula f2 with
                  | FValue false -> FPartial (f1,k1)
                  | FValue true -> FValue true
                  | FPartial (f2,k2) ->
                      if k1 < k2
                      then FPartial (Or (f1,f2), k1+k2)
                      else FPartial (Or (f2,f1), k1+k2)
                end
          end
      | Imply (f1, f2) ->
          begin match eval_formula f1 with
            | FValue true -> eval_formula f2
            | FValue false -> FValue true
            | FPartial (f1,k1) ->
                begin match eval_formula f2 with
                  | FValue false -> FPartial (Not f1,k1)
                  | FValue true -> FValue true
                  | FPartial (f2,k2) -> FPartial (Imply (f1, f2), k1+k2)
                end
          end
      | Iff (f1, f2) ->
          begin match eval_formula f1 with
            | FValue true -> eval_formula f2
            | FValue false -> eval_formula (Not f2)
            | FPartial (f1,k1) ->
                begin match eval_formula f2 with
                  | FValue false -> FPartial (Not f1, k1)
                  | FValue true -> FPartial (f1, k1)
                  | FPartial (f2,k2) ->
                      if k1 < k2
                      then FPartial (Iff (f1, f2), k1+k2)
                      else FPartial (Iff (f2, f1), k1+k2)
                end
          end
      | Forall _ -> Error.fatal "eval_formula: forall encountered"
      | Exists _ -> Error.fatal "eval_formula: exists encountered"
    in

    (* Force [t] to have value [v]. Pass the results, if any, to continuation [k]. *)
    let rec force_term t v k =
      match t with
        | Var i -> Error.fatal "force_term: variable encountered"
        | Elem e -> if v = -1 or e = v then k e
        | Const i ->
            if v = -1 then k (const.(i))
            else if const.(i) = v then k v
        | Unary (op, t) ->
            force_term t (-1)
              (fun w ->
                 if v = -1 then begin
                   if unary.(op).(w) <> -1
                   then k (unary.(op).(w))
                   else begin
                     for u = 0 to n-1 do
                       unary.(op).(w) <- u ;
                       k u
                     done ;
                     unary.(op).(w) <- -1
                   end
                 end
                 else begin
                   if unary.(op).(w) = v then k v
                   else if unary.(op).(w) = -1
                   then begin
                     unary.(op).(w) <- v;
                     k v ;
                     unary.(op).(w) <- -1
                   end
                 end)
        | Binary (op, t1, t2) ->
            force_term t1 (-1)
              (fun w1 -> force_term t2 (-1)
                 (fun w2 ->
                    if v = -1 then begin
                      if binary.(op).(w1).(w2) <> -1
                      then k (binary.(op).(w1).(w2))
                      else begin
                        for u = 0 to n-1 do
                          binary.(op).(w1).(w2) <- u ;
                          k u
                        done ;
                        binary.(op).(w1).(w2) <- -1
                      end
                    end
                    else begin
                      if binary.(op).(w1).(w2) = v then k v
                      else if binary.(op).(w1).(w2) = -1
                      then begin
                        binary.(op).(w1).(w2) <- v;
                        k v ;
                        binary.(op).(w1).(w2) <- -1
                      end
                    end))
    in

    (* When forcing a formula we never have to consider forcing to an unknown truth value
       because that would mean we could have just skipped the formula in the first place.
       Consequently, [force_formula] need not pass any values to the continuation.
    *)
    let rec force_formula f b k =
      match f with
        | True -> if b = 1 then k ()
        | False -> if b = 0 then k ()
        | Predicate (p, t) ->
            force_term t (-1)
              (fun v ->
                 if pred.(p).(v) = -1
                 then begin
                   pred.(p).(v) <- b ;
                   k () ;
                   pred.(p).(v) <- -1
                 end
                 else if pred.(p).(v) = b then k ())
        | Relation (r, t1, t2) ->
            force_term t1 (-1)
              (fun v1 -> force_term t2 (-1)
                 (fun v2 ->
                    if rel.(r).(v1).(v2) = -1
                    then begin
                      rel.(r).(v1).(v2) <- b ;
                      k () ;
                      rel.(r).(v1).(v2) <- -1
                    end
                    else if rel.(r).(v1).(v2) = b then k ()))
        | Equal (t1, t2) ->
            begin match eval_term t1, eval_term t2 with
              | TValue v1, TValue v2 -> if v1 = v2 then k ()
              | TValue v1, TPartial (t2,_) -> force_term t2 v1 (fun _ -> k ())
              | TPartial (t2,_), TValue v2 -> force_term t1 v2 (fun _ -> k ())
              | TPartial (t1,_), TPartial (t2,_) ->
                  force_term t1 (-1)
                    (fun v ->
                       if b = 1
                       then force_term t2 v (fun _ -> k ())
                       else begin
                         for w = 0 to n-1 do
                           if w <> v then force_term t2 w (fun _ -> k ())
                         done
                       end)
            end
        | Not f -> force_formula f (1-b) k
        | And (f1, f2) ->
            if b = 1 then
              force_formula f1 1 (fun () -> force_formula f2 1 k)
            else begin
              force_formula f1 0 k ;
              force_formula f1 1 (fun () -> force_formula f2 0 k)
            end
        | Or (f1, f2) ->
            if b = 0 then
              force_formula f1 0 (fun () -> force_formula f2 0 k)
            else begin
              force_formula f1 1 k ;
              force_formula f1 0 (fun () -> force_formula f2 1 k)
            end
        | Imply (f1, f2) ->
            if b = 0 then
              force_formula f1 1 (fun () -> force_formula f2 0 k)
            else begin
              force_formula f1 0 k ;
              force_formula f1 1 (fun () -> force_formula f2 1 k)
            end
        | Iff (f1, f2) ->
            if b = 0 then begin
              force_formula f1 0 (fun () -> force_formula f2 1 k) ;
              force_formula f1 1 (fun () -> force_formula f2 0 k)
            end
            else begin
              force_formula f1 0 (fun () -> force_formula f2 0 k) ;
              force_formula f1 1 (fun () -> force_formula f2 1 k)
            end
        | Forall _ -> Error.fatal "force_formula: forall encountered"
        | Exists _ -> Error.fatal "force_formula: exists encountered"
    in
      
    let rec fill_relation k =
      let rec g r =
        if r >= Array.length rel then k ()
        else begin
          let rec f (i,j) =
            if i >= n then g (r+1)
            else if rel.(r).(i).(j) = -1
            then
              for b = 0 to 1 do
                rel.(r).(i).(j) <- b ;
                f (if j = n-1 then (i+1,0) else (i,j+1))
              done
            else f (if j = n-1 then (i+1,0) else (i,j+1))
          in
            f (0, 0)
        end
      in
        g 0
    in

    let rec fill_predicate k =
      let rec g p =
        if p >= Array.length pred then k ()
        else begin
          let rec f i =
            if i >= n then g (p+1)
            else if pred.(p).(i) = -1
            then
              for b = 0 to 1 do
                pred.(p).(i) <- b ;
                f (i + 1)
              done
            else f (i + 1)
          in
            f 0
        end
      in
        g 0
    in

    let rec fill_binary k =
      let rec g op =
        if op >= Array.length binary then k ()
        else begin
          let rec f (i,j) =
            if i >= n then g (op+1)
            else if binary.(op).(i).(j) = -1
            then
              for v = 0 to n-1 do
                binary.(op).(i).(j) <- v ;
                f (if j = n-1 then (i+1,0) else (i,j+1))
              done
            else f (if j = n-1 then (i+1,0) else (i,j+1))
          in
            f (0,0)
        end
      in
        g 0
    in

    let rec fill_unary k =
      let rec g op =
        if op >= Array.length unary then k ()
        else begin
          let rec f i =
            if i >= n then g (op+1)
            else if unary.(op).(i) = -1
            then
              for v = 0 to n-1 do
                unary.(op).(i) <- v ;
                f (i + 1)
              done
            else f (i + 1)
          in
            f 0
        end
      in
        g 0
    in

    let rec prepare_formula = function
      | (True _ | False _ | Equal _ | Predicate _ | Relation _) as f -> f
      | Forall (i, f) -> prepare_formula (and_of n i f)
      | Exists (i, f) -> prepare_formula (or_of n i f)
      | Not f -> Not (prepare_formula f)
      | And (f1, f2) -> And (prepare_formula f1, prepare_formula f2)
      | Or (f1, f2) -> Or (prepare_formula f1, prepare_formula f2)
      | Imply (f1, f2) -> Imply (prepare_formula f1, prepare_formula f2)
      | Iff (f1, f2) -> Iff (prepare_formula f1, prepare_formula f2)
    in

    let prepare_equation (i, (t1, t2)) =
      prepare_formula
        (List.fold_right (fun x g -> Forall (x, g)) (Util.enumFromTo 0 (i-1)) (Equal (t1, t2)))
    in

    let prepare_axioms eqs axs =
      let rec conjuncts acc = function
        | True -> acc
        | And (f1, f2) -> conjuncts (conjuncts acc f1) f2
        | f -> f :: acc
      in
        List.sort compare_partial_formulas
          (List.map eval_formula
             (List.fold_left (fun cs (_,f) -> conjuncts cs (prepare_formula f))
                (List.fold_left (fun cs e -> conjuncts cs (prepare_equation e)) [] eqs) axs))
    in

    let simplify_conjuncts cs =
      let rec loop acc = function
        | [] -> acc
        | FValue true :: cs -> loop acc cs
        | FValue false :: cs -> []
        | FPartial (f,_) :: cs -> loop (eval_formula f :: acc) cs
      in
        List.sort compare_partial_formulas (loop [] cs)
    in

    let rec force_conjuncts cs k =
      let cs =
        (match cs with
           | [] -> []
           | FValue _ :: _ -> cs
           | FPartial (_,k) :: _ ->
               if k <= 1
               then cs
               else simplify_conjuncts cs)
      in
        match cs with
          | [] -> k ()
          | (FValue true) :: cs -> force_conjuncts cs k
          | (FValue false) :: _ -> ()
          | (FPartial (f,_)) :: cs -> force_formula f 1 (fun () -> force_conjuncts cs k)              
    in

    (* Body of the main function *)
    let cs = prepare_axioms eqs axs in
      force_conjuncts cs
        (fun () -> fill_unary
           (fun () -> fill_binary
              (fun () -> fill_predicate
                 (fun () -> fill_relation
                    (fun () -> k a)))))

  end
