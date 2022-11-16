module SpecToLH where
import Language.Haskell.Liquid.Types
import qualified Language.Fixpoint.Types as F
import qualified Data.Bifunctor as B
import Debug.Trace

import qualified LH
import Util

transCon :: RTyCon -> LH.Type
transCon (RTyCon tc pvars info) = LH.TDat (showppStripped tc) $ map (LH.TVar . showpp) pvars

showppStripped :: PPrint a => a -> String
showppStripped = strip . showpp

retType :: SpecType -> LH.LHArg
retType (RFun _ _ _ t_out _) = retType t_out
retType t = LH.LHArg "@retType" `uncurry` trans t

-- isProof :: SpecType -> Bool
-- isProof t = showppStripped (rt_bind (retType t)) == "()"

transArgs :: SpecType -> [LH.LHArg]
transArgs (RFun id _ t_in t_out _) =
  LH.LHArg (showppStripped id) `uncurry` trans t_in : transArgs t_out
transArgs _ = []

trans :: SpecType -> (LH.Type, LH.LHExpr)
trans (RApp con _ _ reft) = (transCon con, snd $ transRReft reft)
trans sp = error $ "undefined translation from LH SpecType to LH.TypeExpr: \n"
                ++ showpp sp

transRReft :: RReft -> (Id, LH.LHExpr)
transRReft = B.bimap showppStripped transExpr . unreft . ur_reft

unreft (F.Reft t) = t
transExpr :: F.Expr -> LH.LHExpr
transExpr (F.PAtom brel e1 e2) = LH.Brel (transBrel brel) (transExpr e1) (transExpr e2)
transExpr app@F.EApp{}         = uncurry LH.LHApp $ flattenApp app
transExpr (F.EVar sym)         = LH.LHVar (showppStripped sym)
transExpr (F.PAnd [])          = LH.LHVar "True"
transExpr (F.PAnd [e])         = transExpr e
transExpr (F.PAnd es)          = LH.And $ map transExpr es
transExpr e = error $ "undefined expr translation: \n"
                    ++ showpp e

flattenApp :: F.Expr -> (Id, [LH.LHExpr])
flattenApp (F.EApp f x) = (++ [transExpr x]) `B.second` flattenApp f
flattenApp (F.EVar name) = (showppStripped name, [])

transSig :: SpecType -> LH.Signature
transSig f = LH.Signature (transArgs f) (retType f)

transBrel :: F.Brel -> LH.Brel
transBrel F.Eq = LH.Eq
transBrel _    = error "undefined brel translation"