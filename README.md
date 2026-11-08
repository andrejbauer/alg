# Alg

Alg is a program for enumeration of finite models of first-order theories, with the following constraints:

* the theory must be single-sorted,
* only unary and binary operations are accepted,
* only unary predicates and binary relations are accepted,
* it is assumed that constants denote pariwise distinct elements.

## Installation

The preferred way to install Alg is with the OCaml package manager [Opam](https://opam.ocaml.org), directly from the GitHub repository:

    opam pin add alg https://github.com/andrejbauer/alg.git

This compiles and installs the `alg` executable, and places example theories in the `share/alg/theories` directory of the opam switch.

Run `opam upgrade alg` to update Alg to the latest version, and `opam remove alg` to remove it.

## Compilation from source

To compile Alg you need [OCaml](https://ocaml.org), the [dune](https://dune.build) build system, and the [menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, all available through Opam:

    opam install dune menhir dune-build-info

Then run

    dune build

in the Alg source directory. The executable `alg.exe` appears in the top directory, so you can test it by running

    ./alg.exe theories/group.th --size 1-9 --axiom 'x * x = 1'

to enumerate all groups of size at most 9 in which all elements have rank 2.

Run `dune test` to run the tests.

## Usage

See the manual [`MANUAL.md`](MANUAL.md) and the examples in the [`./theories`](./theories) folder.
