# Alg


Alg is a program for enumeration of finite models of first-order theories. Currently, Alg has the following limitations:

* the theory must be single-sorted,
* only unary and binary operations are accepted,
* only unary predicates and binary operations are accepted,
* it is assumed that constants denote pariwise distinct elements.

## Installation

### Prerequisites

Alg is available at [http://www.andrej.com/alg/] (which currently just redirects to GitHub). Apart from the source code, you will need the following:

* [OCaml](https://ocaml.org) compiler, which you can very likely install using a package manager. Every Linux distribution comes with one, while on MacOS you can use [Homebrew](https://brew.sh).

* If you are going to use OCaml for other projects, it is a good idea to install the OCaml package manager [OPAM](https://opam.ocaml.org) and use that instead of your default package manager. (It does requite a bit of configuration, though.)

* The [ocamlbuild](https://ocaml.org/learn/tutorials/ocamlbuild/) compilation tool for OCaml, available through your package manager, e.g.,

    * Linux: `sudo apt-get install ocamlbuild`
    * OPAM: `opam install ocamlbuild`
    * Homebrew: `brew install ocamlbuild`


* The [menhir](http://gallium.inria.fr/~fpottier/menhir/) parser generator, available through your package manager, e.g.,

    * Linux: `sudo apt-get install caml-menhir`
    * OPAM: `opam install menhir`
    * Homebrew: `brew install menhir`

With sufficient user base I could probably be convinced to support at least a Homebrew package for Alg.

### Compilation

If all goes well you should be able to compile Alg simply by running

    make

in the Alg source directory. This will generate the executable, which you can test by running

    ./alg.native theories/group.th --size 1-9 --axiom 'x * x = 1'

to enumerate all groups of size at most 9 in which all elements have rank 2.

The compilation procedure also generates the Alg manual `doc/manual.pdf`. It relies on LaTeX. If you do not have it (how can that be?) you may compile just the executable by running

    make ./alg.native

