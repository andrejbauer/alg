# alg
Alg is a program for enumeration of finite models of single-sorted
first-order theories. Such a theory is given by a signature (a list of
constants, operations and relations) and axioms expressed in
first-order logic. Examples of first-order theories include groups,
lattices, rings, fields, posets, graphs, and many others.

Currently alg has the following limitations:
* the theory must be single-sorted,
* only unary and binary operations are accepted,
* only (unary) predicates and binary relations are accepted,
* it is assumed that constants denote pairwise distinct elements.

## Requirements
* Ocaml 3.11 or newer 
* the menhir parser generator

## Installation
Compile alg with `make` and run `./src/alg.native --size 8 theories/unital_commutative_ring.th`
For usage information type `./alg.native -help` and for
examples of theories see the `theories` subdirectory.
