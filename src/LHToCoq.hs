module LHToCoq (run) where

import CoreSyn(CoreBind)

import qualified Liquid.GHC.Interface as LH (getTargetInfos)
import qualified Language.Haskell.Liquid.Types as LH 
import qualified Language.Haskell.Liquid.UX.CmdLine as LH (getOpts)
import qualified Coq(Def(..), Id)
import qualified Data.Map as M
import qualified Data.Bifunctor as B

import Translate
import Util

run :: [String] -> IO ()
run args = do 
  (binds,specs) <- getBindsAndSpecs args

  let coqDefs = map transBind binds
  let specMap = M.fromList specs
  
  mapM_ print $ pairDefsWithSpecs coqDefs specMap

type SpecPair = (Coq.Id, LH.SpecType)

-- Get the stuff that we need from LH parser, namely: Binds and Specs.
-- @args has the filename inside (and other flags that we might have set).
getBindsAndSpecs :: [String] -> IO ([CoreBind], [SpecPair])
getBindsAndSpecs args = do
  cfg                            <- LH.getOpts args
  (LH.TargetInfo src specs:_, _) <- LH.getTargetInfos Nothing cfg (LH.files cfg)
  
  return (LH.giCbs src, getSpecPairs specs)

  where getSpecPairs :: LH.TargetSpec -> [SpecPair]
        getSpecPairs = map (B.bimap showStripped LH.val) . LH.gsTySigs . LH.gsSig

-- Some of the definitions don't have specs AND THAT'S OK! (they will be paired with Nothing)
pairDefsWithSpecs :: [Coq.Def] -> M.Map Coq.Id LH.SpecType -> [(Coq.Def, Maybe LH.SpecType)]
pairDefsWithSpecs defs specMap = foldl (\acc d -> single d : acc) [] defs
  where single :: Coq.Def -> (Coq.Def, Maybe LH.SpecType)
        single def@(Coq.Def id _ ) =  (def, M.lookup id specMap)
