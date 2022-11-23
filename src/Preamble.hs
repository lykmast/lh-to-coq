module Preamble(preamble) where

preamble :: [String]
preamble = natDecl : ltacs
  where
    ltacs = [ple, smtTrivial, smtApp, smtSolve]
    natDecl    = "Inductive PNat:Set := Z : PNat | S: PNat -> PNat."
    ple        = "Ltac ple := simpl."
    smtTrivial = "Ltac smt_trivial := simpl; first [ assumption | intuition discriminate | easy]."
    smtApp     = "Ltac smt_app th := first "   ++ appTacList ++ "."
    smtSolve   = "Ltac smt_solve th := solve [ now rewrite th | now ple; rewrite th | now apply th | now ple; apply th]."
    appTacList = "[ rewrite th | ple; rewrite th | apply th | ple; apply th]"
