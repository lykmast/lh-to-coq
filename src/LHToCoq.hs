module LHToCoq (run) where

import CoreSyn
import qualified Liquid.GHC.Interface as LhLib (getTargetInfos)
import qualified Language.Haskell.Liquid.Types as LhLib
import qualified Language.Haskell.Liquid.UX.CmdLine as LhLib (getOpts)
import qualified Data.Map as M
import qualified Data.Bifunctor as B

import qualified CoreToLH as CLH
import qualified LH
import qualified SpecToLH as SLH
import Util


run :: [String] -> IO ()
run args = do 
    (binds,specs) <- B.first (filter (not . isDollarBind)) <$> getBindsAndSpecs args
    let
      specMap = SLH.transSig <$> M.fromList specs
      lhDefs = map CLH.transBind binds
      (defs, proofs) = splitDefsAndProofs $ pairLHDefsWithSigs lhDefs specMap
      coqDefs    = map LH.transDef defs
      mCoqProofs = map LH.transLH proofs

    mapM_ putStrLn preamble
    mapM_ print coqDefs
    mapM_ print mCoqProofs

preamble :: [String]
preamble = natDecl : ltacs
  where
    ltacs = [ple, smtTrivial, smtApp]
    natDecl    = "Inductive PNat:Set := Z : PNat | S: PNat -> PNat."
    ple        = "Ltac ple := simpl."
    smtTrivial = "Ltac smt_trivial := try intuition discriminate."
    smtApp     = "Ltac smt_app th := first [ rewrite th | ple; rewrite th ]."

type SpecPair = (Id, LhLib.SpecType)

-- Get the stuff that we need from LH parser, namely: Binds and Specs.
-- @args has the filename inside (and other flags that we might have set).
getBindsAndSpecs :: [String] -> IO ([CoreBind], [SpecPair])
getBindsAndSpecs args = do
    cfg <- LhLib.getOpts args
    (LhLib.TargetInfo src specs:_, _)
      <- LhLib.getTargetInfos Nothing cfg (LhLib.files cfg)
    return (LhLib.giCbs src, getSpecPairs specs)
  where 
    getSpecPairs :: LhLib.TargetSpec -> [SpecPair]
    getSpecPairs = map (B.bimap showStripped LhLib.val) . LhLib.gsTySigs . LhLib.gsSig

pairLHDefsWithSigs :: [LH.Def] -> M.Map Id LH.Signature -> [(LH.Def, Maybe LH.Signature)]
pairLHDefsWithSigs defs specMap = map single defs
  where
    single :: LH.Def -> (LH.Def, Maybe LH.Signature)
    single def@(LH.Def id _ _) =  (def, M.lookup id specMap)


splitDefsAndProofs :: [(LH.Def, Maybe LH.Signature)] -> ([LH.Def], [LH.Proof])
splitDefsAndProofs pairs = (defs, proofs)
  where
    (defsWithSig, defsWithNoSig) = partition (isJust . snd) pairs
    (proofDefs, noProofDefs) =
        partition (LH.isProof . snd) $ map (B.second fromJust) defsWithSig
    defs   = map fst defsWithNoSig ++ map fst noProofDefs
    proofs = map (uncurry LH.Proof) proofDefs

isDollarBind :: Show b => Bind b -> Bool
isDollarBind (NonRec b _)    = head (showStripped b) == '$'
isDollarBind (Rec ((b,_):_)) = head (showStripped b) == '$'