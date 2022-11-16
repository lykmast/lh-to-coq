module CoreToLH where

import CoreSyn
import qualified Liquid.GHC.Interface() -- show instances for some GHC things.
import Data.Bifunctor as B

import qualified LH
import Util

-- Top level binds.
transBind :: Show b => Bind b -> LH.Def
transBind  (NonRec b e) =
  LH.Def (showStripped b) `uncurry` flattenFun e
transBind  (Rec ((b,e): _)) =
  LH.Def (showStripped b) `uncurry` flattenFun e

-- Expressions.
trans :: Show b => Expr b -> LH.Expr
trans (Var id)  | name == "()" = LH.Unit 
                | otherwise = LH.Var name
                where name = showStripped id
trans app@App{}
  | name == "?" = LH.QMark first second
  | name == "patError" = LH.Unit -- patError parts replaced by trivial.
  | name == "()" = LH.Unit
  | otherwise   = LH.App name args
  where (name, args)     = flattenApp app
        (_:_:first:second:_) = args
trans l@Lam{}            = error "lambda expression not supported."
trans (Case e b t alts)  = LH.Case (trans  e) (showStripped b) (map altToClause alts)
trans c@Cast{}           = error "cast expression not supported."
trans (Tick tick e)      = trans e -- ignore ticks
trans (Type t)           = LH.Var "[@type]"
trans c@Coercion{}       = error "coercion expression not supported."
trans (Let bind e) =
    case e' of
      Lit{} -> trans e  -- ignore let lit (part of patError)
      _     -> LH.Let (show x) (trans e') (trans e)
  where
    (x, e') = deconstructBind bind
trans l@Lit{} = LH.Var "[@lit]"
-- Deconstruct binds.

deconstructBind :: Bind b -> (b, Expr b)
deconstructBind (Rec ((b,e):_) ) = (b, e)
deconstructBind (NonRec b e)     = (b, e)

-- case-of branches.
altToClause :: Show b => Alt b -> (LH.Pat, LH.Expr)
altToClause (con, bs, e) = (LH.Pat (go con) (map showStripped bs), trans e)
  where go :: AltCon -> String
        go (DataAlt dc) = showStripped dc
        go (LitAlt lit) = "LitAltTODO"
        go DEFAULT      = "_"

flattenFun :: Show b => Expr b -> ([Id], LH.Expr)
flattenFun (Lam b e) = B.first (showStripped b:) $ flattenFun e
flattenFun e         = ([], trans e)

flattenApp :: Show b => Expr b -> (Id, [LH.Expr])
flattenApp (App f x) = (++ [trans x]) `B.second` flattenApp f
flattenApp (Var name) = (showStripped name, [])
flattenApp t          = error "cannot flatten expr."