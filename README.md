# lh-to-coq

Translate Liquid Haskell to Coq.

All `lh-examples/*.hs` files have valid Coq translations: (https://github.com/lykmast/lh-to-coq/actions/workflows/coq-test.yml/badge.svg)

### Status
Print Coq definitions and proofs for corresponding Haskell definitions and LH proofs.

[Simple.hs](lh-examples/Simple.hs) is succesfully translated. In [Fact.hs](lh-examples/Fact.hs) some work is needed to translate refined arguments and boolean predicates such as `leb` 

### Run example
```
stack run -- "lh-examples/Simple.hs" 
```
