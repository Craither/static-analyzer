(lang dune 3.13)
(using menhir 3.0)

(name analyzer)

(generate_opam_files true)

(authors "INRIA/CNRS/ENS PLS")

(maintainers "Charles de Haro")

(package
  (name analyzer)
  (depends
    dune
    zarith
    menhir))
