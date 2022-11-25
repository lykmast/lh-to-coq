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
import           Simplify (simplify)
import Preamble (preamble)
import Util


run :: [String] -> IO ()
run args = do
    (binds,specs) <- B.first (filter (not . isIgnoredBind)) <$> getBindsAndSpecs args
    let
      specMap = SLH.transSig <$> M.fromList specs
      lhDefs = map CLH.transBind (simplify <$> binds)
      (defs, proofs) = splitDefsAndProofs $ pairLHDefsWithSigs lhDefs specMap
      coqDefs    = map LH.transDef defs
      mCoqProofs = map LH.transLH proofs

    mapM_ putStrLn preamble
    mapM_ print coqDefs
    mapM_ print mCoqProofs

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

isIgnoredBind :: Show b => Bind b -> Bool
isIgnoredBind bind = name `startsWith` '$' || name == "?"
  where
    name = showStripped $
      case bind of
        NonRec b _    -> b
        Rec ((b,_):_) -> b
    startsWith xs c = c == head xs

