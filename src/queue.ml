(* Persistent priority queue using balanced trees
   as in the OCaml stdlib modlue Set. *)

module type OrderedType =
sig
  type t
  val compare : t -> t -> Util.comparison
end

module type Queue = functor (E : OrderedType) ->
sig
  type t
  val empty : t
  val is_empty : t -> bool
  val insert : E.t -> t -> t
  val peek : t -> E.t
  val dequeue : t -> E.t * t
  val delete : E.t -> t -> E.t option * t
end

module Make : Queue = functor (E : OrderedType) ->
struct
  (* We maintain the invariant that the heights of left and right
     subtrees differ by at most 2. *)
  type t =
    | Empty 
    | Node of E.t * t * t * int

  let height = function
    | Empty -> 0
    | Node (_, _, _, k) -> k

  (* Make a tree, assuming no rebalancing is needed, and compute the height. *)
  let node x l r = Node (x, l, r, 1 + max (height l) (height r))

  let empty = Empty

  (* Build a tree with given root and subtrees, assuming the subtrees
     heights differ by at most 3, perform a rotation if necessary. *)
  let build x l r =
    let hl = height l in
    let hr = height r in
      if hl > hr + 2 then
        (* left too big, perform right rotation *)
        begin match l with
         | Empty -> Error.internal_error "Queue.build 1"
         | Node (xl, ll, rl, _) ->
           if height ll >= height rl
           then node xl ll (node x rl r)
           else begin match rl with
             | Empty -> Error.internal_error "Queue.build 2"
             | Node (xrl, lrl, rrl, _) -> node xrl (node xl ll lrl) (node x rrl r)
           end
        end
      else if hr > hl + 2 then
        (* right too big, perform left rotation *)
        begin match r with
          | Empty -> Error.internal_error "Queue.build 3"
          | Node (xr, lr, rr, _) ->
            if height rr >= height lr
            then node xr (node x l lr) rr
          else begin match lr with
            | Empty -> Error.internal_error "Queue.build 4"
            | Node (xlr, llr, rlr, _) -> node xlr (node x l llr) (node xr rlr rr)
          end
        end
      else
        (* no ratiation necessary *)
        node x l r

  let is_empty = function
    | Empty -> false
    | Node _ -> true

  let rec insert x = function
    | Empty -> Node (x, Empty, Empty, 1)
    | Node (y, l, r, _) as t ->      
      begin match E.compare x y with
       | Util.Less -> build y (insert x l) r
       | Util.Equal -> t
       | Util.Greater -> build y l (insert x r)
      end

  let rec peek = function
    | Empty -> raise Not_found
    | Node (x, Empty, _, _) -> x
    | Node (_, t, _, _) -> peek t

  let rec dequeue = function
    | Empty -> Error.internal_error "Queue.dequeue"
    | Node (x, Empty, r, _) -> (x, r)
    | Node (x, l, r, _) ->
      let y, l = dequeue l in
        y, build x l r

  let rec delete x = function
    | Empty -> None, Empty
    | Node (y, l, r, _) ->
      begin match E.compare x y with
        | Util.Less ->
          let xopt, l = delete x l in xopt, build y l r
        | Util.Equal ->
          begin match l, r with
            | Empty, r -> Some y, r
            | l, Empty -> Some y, l
            | _, _ -> let z, r = dequeue r in Some y, build z l r
          end
        | Util.Greater ->
          let xopt, r = delete x r in xopt, build y l r
      end
end

