(lang dune 3.16)
(using coq 0.8)
(name coq2cakeml)
(version 0.1)

(package
 (name coq2cakeml)
 (depends
  (coq (= 8.17.1))
  (coq-equations (= 1.3+8.17))
  (dune (= 3.16.0))
  (cakeml-semantics (= 0.1)))
 (synopsis "Coq plugin to synthesize CakeML from Coq")
 (description  "")
 (maintainers   "tjbarclay@ku.edu")
 (authors      "TJ Barclay")
)

(generate_opam_files true)
