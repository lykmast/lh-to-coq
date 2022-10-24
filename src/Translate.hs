module Translate(trans, transBind) where

import CoreSyn
import qualified Liquid.GHC.Interface() -- show instances for some GHC things.
import qualified Coq

import Util

-- Top level binds.
transBind :: Show b => Bind b -> Coq.Def
transBind  (NonRec b e) =
  Coq.Def (showStripped b) (trans  e) 
transBind  (Rec ((b,e): _)) =
  Coq.Def (showStripped b) (trans  e) 

-- Expressions.
trans :: Show b => Expr b -> Coq.Expr
trans (Var id)          = Coq.Var (showStripped id)
trans (App f x)         = Coq.App (trans f) (trans x)
trans (Lam b e)         = Coq.Fun (showStripped b) (trans e)
trans (Case e b t alts) = Coq.Match (trans  e) (showStripped b) (map altToClause alts)
trans (Cast e coercion) = Coq.Var "[@cast]"
trans (Tick tick e)     = trans e -- ignore ticks
trans (Type t)          = Coq.Var "[@type]"
trans (Coercion c)      = Coq.Var "[@coercion]"
trans (Let bind e)      = Coq.Let (showStripped (bindB bind)) (trans (bindExpr bind)) (trans e)
trans (Lit l)           = Coq.Var "[@lit]"

-- Deconstruct binds.
bindExpr :: Bind b -> Expr b
bindExpr (Rec ((b,e):_) ) = e
bindExpr (NonRec b e) = e

bindB :: Bind b -> b
bindB (Rec ((b,e):_) ) = b
bindB (NonRec b e) = b

-- case-of branches.
altToClause :: Show b => Alt b -> (Coq.Pat, Coq.Expr)
altToClause (con, bs, e) = (Coq.Pat (go con) (map showStripped bs), trans e)
  where go :: AltCon -> String
        go (DataAlt dc) = showStripped dc
        go (LitAlt lit) = "LitAltTODO"
        go DEFAULT      = "_"