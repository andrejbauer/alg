(lang dune 3.11)

(name alg)

(generate_opam_files)

(using menhir 2.1)

(source
 (github andrejbauer/alg))

(license BSD-2-Clause)

(authors "Ales Bizjak" "Andrej Bauer")

(maintainers "Andrej Bauer <Andrej.Bauer@andrej.com>")

(package
 (name alg)
 (synopsis "Enumeration of finite models of first-order theories")
 (description
  "Alg is a program for enumeration of finite models of first-order theories.")
 (depends
  (ocaml
   (>= 4.08))
  menhir
  dune-build-info))
