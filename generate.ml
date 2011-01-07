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
let generate n ({T.th_const=const; T.th_equations=eqs; T.th_axioms=axs} as th) k =
  if n >= Array.length const then begin
    let a = Algebra.empty n th in
    let const = a.alg_const in
    let unary = a.alg_unary in
    let binary = a.alg_binary in
    let pred = a.alg_predicates in
    let rel = a.alg_relations in

    (* Force [t] to have value [v]. *)
    let rec force_term t v k =
      match t with
        | T.Var i -> Error.fatal "force_term: variable encountered"
        | T.Elem e -> if v = -1 or e = v then k e
        | T.Const i ->
            if v = -1 then k (const.(i))
            else if const.(i) = v then k v
        | T.Unary (op, t) ->
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
        | T.Binary (op, t1, t2) ->
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
            force_term t1 (-1)
              (fun v ->
                 if b = 1
                 then force_term t2 v (fun _ -> k ())
                 else begin
                   for w = 0 to n-1 do
                     if w <> v then force_term t2 w (fun _ -> k ())
                   done
                 end)
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
        | Forall (i, f) ->
            force_formula (and_of n i f) b k
        | Exists (i, f) ->
            force_formula (or_of n i f) b k
    in
      
    let force_equation (i,(t1,t2)) b k =
      let f = List.fold_right (fun x g -> Forall (x, g)) (Util.enumFromTo 0 (i-1)) (Equal (t1, t2)) in
        force_formula f b k
    in
      
    let rec force_equations eqs k =
      match eqs with
        | [] -> k ()
        | eq :: eqs -> force_equation eq 1 (fun () -> force_equations eqs k)
    in

    let rec force_axioms axs k =
      match axs with
        | [] -> k ()
        | (_,ax) :: axs -> force_formula ax 1 (fun () -> force_axioms axs k)
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

      force_equations eqs
        (fun () -> force_axioms axs
           (fun () -> fill_unary
              (fun () -> fill_binary
                 (fun () -> fill_predicate
                    (fun () -> fill_relation
                       (fun () -> k a))))))
        
  end
