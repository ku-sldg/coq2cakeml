(lang dune 3.16)
(using coq 0.8)
(name coq2cakeml)
(version 0.1)

(package
 (name coq2cakeml)
 (depends
  coq
  coq-equations
  dune
  cakeml-semantics)
 (synopsis "Coq plugin to synthesize CakeML from Coq")
 (description  "")
 (maintainers   "tjbarclay@ku.edu")
 (authors      "TJ Barclay")
)

(generate_opam_files true)
