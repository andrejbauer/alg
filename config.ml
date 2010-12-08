(* Options for command-line arguments. *)

type config = {
  mutable sizes : int list;
  mutable indecomposable_only : bool;
  mutable count_only : bool;
  mutable products : bool;
  mutable source : bool;
  mutable input_filename : string;
}

let default = {
  sizes = [];
  indecomposable_only = false;
  count_only = false;
  products = true;
  source = true;
  input_filename = "";
}
