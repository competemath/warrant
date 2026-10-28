(lang dune 3.16)

(name warrant)

(generate_opam_files true)

(license Apache-2.0)

(authors "WARRANT contributors")

(maintainers "Mikael Bashir")

(source
 (github competemath/warrant))

(package
 (name warrant)
 (synopsis "A Lean 4 kernel whose only currency is provenance-indexed evidence")
 (description
  "WARRANT checks lean4export files. Every fact the checker relies on is an evidence value minted by one function and stamped with the environment it holds in; metadata in a file is a claim that becomes a fact only by re-derivation.")
 (depends
  (ocaml
   (>= 5.3))
  (dune
   (>= 3.16))
  (zarith
   (>= 1.12))
  (yojson
   (>= 2.0))
  (alcotest :with-test)
  (qcheck-core :with-test)
  (qcheck-alcotest :with-test)
  (ocamlformat
   (and
    :with-dev-setup
    (= 0.29.0)))))
