(* Algebras are models of theories. *)

type algebra = {
  mutable alg_name : string option;
  alg_prod : string list option;
  alg_size : int array;
  alg_const : int array;
  alg_unary : int array array;
  alg_binary : int array array array;
  alg_predicates : int array array;
  alg_relations : int array array array;
}

(* An algebra for the given sizes and theory, with all -1's indicating "completely
   undefined". *)
let empty ns
    {Theory.th_sort=s;
     Theory.th_const=c;
     Theory.th_unary=u;
     Theory.th_binary=b;
     Theory.th_predicates=p;
     Theory.th_relations=r} =
  if Array.length ns <> Array.length s
  then Error.internal_error ~loc:Common.Nowhere "Algebra.empty: invalid size argument" ;
  {
    alg_name = None;
    alg_prod = None;
    alg_size = ns;
    alg_const =
      begin
        let c_count = Array.make (Array.length s) (-1) in
        Array.map (fun (_,k) ->
          c_count.(k) <- c_count.(k) + 1 ;
          if c_count.(k) >= ns.(k) then
            Error.internal_error ~loc:Common.Nowhere
              "Algebra.empty: too many constants of sort %s" s.(k) ;
          c_count.(k))
          c ;
      end ;
    alg_unary = Array.map (fun (_,k,_) -> Array.make ns.(k) (-1)) u;
    alg_binary = Array.map (fun (_,k1,k2,_) -> Array.create_matrix ns.(k1) ns.(k2) (-1)) b;
    alg_predicates = Array.map (fun (_,k) -> Array.make ns.(k) (-1)) p;
    alg_relations = Array.map (fun (_,k1,k2) -> Array.create_matrix ns.(k1) ns.(k2) (-1)) r
  }
