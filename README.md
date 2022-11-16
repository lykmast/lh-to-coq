# lh-to-coq

Translate Liquid Haskell to Coq.

### Status
Print Coq definitions and proofs for corresponding Haskell definitions and LH proofs.

[Simple.hs](lh-examples/Simple.hs) is succesfully translated. In [Fact.hs](lh-examples/Fact.hs) some work is needed to translate refined arguments and boolean predicates such as `leb` 

### Run example
```
stack run -- "lh-examples/Simple.hs" 
```
