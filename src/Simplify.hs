{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TupleSections        #-}

module Simplify (simplify) where

import CoreSyn
import Var
import qualified Liquid.GHC.Interface () -- show instances for some GHC things.

import Data.List (lookup, notElem, isPrefixOf)
import Util      (mapSnd, mapMSnd, showStripped)
import Control.Monad.State.Lazy

class Simplifiable a where
  simplify :: a -> a

instance Simplifiable CoreBind where
  simplify (NonRec x e) = NonRec x (simplify e)
  simplify (Rec xes)    = Rec (mapSnd simplify xes)

instance Simplifiable CoreExpr where
  simplify e = let (e', su) = grapANFs e in subst su e'

-------------------------------------------------------------------------------
-- | Grap ANF -----------------------------------------------------------------
-------------------------------------------------------------------------------

grapANFs :: CoreExpr -> (CoreExpr, Subst)
grapANFs e = (e',su')
  where
    (e',su) = runState (go e) []
    su' = fix f su
    f su0 = [ (x,subst su0 ex) | (x,ex) <- su0]
    fix f x = let x' = f x in if x == x' then x else fix f x'
    go (Let (NonRec x ex) e)
      | isANFVar x = do {ex' <- go ex; modify ((x,ex'):); go e}
      | otherwise  = do {ex' <- go ex; Let (NonRec x ex') <$> go e}
    go (Let (Rec xes) e)
      = do xes' <- mapMSnd go xes
           Let (Rec xes') <$> go e
    go (App e1 e2) = do {e1' <- go e1; e2' <- go e2; return (App e1' e2')}
    go (Lam x e) = Lam x <$> go e
    go (Case e x t alts) = do
        e' <- go e
        Case e' x t <$> mapM goAlts alts
    go (Cast e c)     = (`Cast` c) <$> go e
    go (Tick t e)     = Tick t <$> go e
    go e@(Type _)     = return e
    go e@(Coercion _) = return e
    go e@(Lit _)      = return e
    go e@(Var _)      = return e

    goAlts (c, xs, e) = (c,xs,) <$> go e

isANFVar :: Var -> Bool
isANFVar = isPrefixOf "lq_anf" . showStripped

-------------------------------------------------------------------------------
-- | Substitutions ------------------------------------------------------------
-------------------------------------------------------------------------------

type Subst = [(Var,CoreExpr)]

class Subable a where
  subst :: Subst -> a -> a

instance Subable CoreExpr where
  subst su (Var x)
    | Just e <- lookup x su = e
    | otherwise             = Var x
  subst _ (Lit l) = Lit l
  subst su (App e1 e2)       = App (subst su e1) (subst su e2)
  subst su (Lam x e)         = Lam x (subst su' e)
    where su' = filter ((/= x) . fst) su
  subst su (Let b e)         = Let (subst su b) (subst su' e)
    where su' = filter ((`notElem` binds b) . fst) su
  subst su (Case e x t alts) = Case (subst su e) x t (subst su' alts)
    where su' = filter ((/= x) . fst) su
  subst su (Cast e c)        = Cast (subst su e) c
  subst su (Tick t e)        = Tick t (subst su e)
  subst _ (Type t)           = Type t
  subst _ (Coercion c)       = Coercion c

instance Subable CoreAlt where
  subst su (c, xs, e) = (c, xs, subst su' e)
    where su' = filter ((`notElem` xs) . fst) su

instance Subable a => Subable [a] where
  subst su es = subst su <$> es

instance Subable CoreBind where
  subst su (NonRec x e) = NonRec x (subst su' e)
    where su' = filter ((/= x) . fst) su
  subst su (Rec xes)    = Rec (mapSnd (subst su') xes)
    where su' = filter ((`notElem` (fst <$> xes)) . fst) su

binds :: CoreBind -> [Var]
binds (NonRec x _) = [x]
binds (Rec xes)    = fst <$> xes

instance Eq CoreExpr where
  e1 == e2 = show e1 == show e2