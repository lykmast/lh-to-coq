# lh-to-coq

Translate Liquid Haskell to Coq.

All `lh-examples/*.hs` files have valid Coq translations: ![Status:](https://github.com/lykmast/lh-to-coq/actions/workflows/coq-test.yml/badge.svg)

### Status

Print Coq definitions and proofs for corresponding Haskell definitions and LH proofs.
[Simple.hs](lh-examples/Simple.hs) and [Fact.hs](lh-examples/Fact.hs) are succesfully translated.

Cases covered are (possibly) inductive proofs on peano natural numbers.

### Running examples

Examples can be compiled to Coq by running [test.sh](test.sh), which will create `.v` files in [out](out).
To typecheck the `.v` files with Coq, run `coqc file.v` (or open the file in an interactive Coq environment).
