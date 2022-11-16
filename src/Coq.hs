module Coq where
import Util


data Proof = Proof {cpName :: Id, cpArgs :: [(Id,Type)], cpType :: Prop, cpbody :: [Tactic]}
instance Show Proof where
  show (Proof name args ty bod) =
    "Theorem " ++ name ++ " " ++ unwords (map showArg args) ++ ": " ++ show ty ++ ".\n"
    ++ "Proof.\n"
    ++ intercalate ". " (map show bod) ++ ".\n"
    ++ "Qed.\n"
-- data Proof = IndProof {bod :: ProofBod  , proofIndArg :: (Id,Int)} | NIndProof {bod :: PrBod}
showArg :: (Id,Type) -> String
showArg (arg, t) = addParens $ arg ++ ": " ++ show t

data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr}
instance Show Def where
  show (Def name args body) =
    "Fixpoint " ++ name ++ " " ++ unwords args ++ " :=\n"
    ++ "  " ++ show body ++ ".\n"
  
data Pat = Pat {patCon :: Id, patArgs :: [Id]}

instance Show Pat where
  show (Pat c args) = c ++ " " ++ unwords (map filterWeird args)

data Expr = App Id [Expr]
          | Var Id
          | Match Expr Id [(Pat, Expr)]
          | Let Id Expr Expr

instance Show Expr where
  show (App f []) = filterWeird f
  show (App f es) = f ++ " " ++ unwords (map showAppArg es)
  show (Var id) = filterWeird id
  show (Let id b e) = "let " ++ filterWeird id ++ " := " ++ show b ++ " in " ++ show e
  show (Match e id branches) =
      "match " ++ show e ++ " as " ++ filterWeird id ++ " with "
      ++ unwords (map showBranch branches) ++ " end"
    where
      showBranch (p, e) = "| " ++ show p ++ " => " ++ show e

showAppArg :: Expr -> String
showAppArg app@(App _ (_:_)) = addParens $ show app
showAppArg e = show e

data Type = TExpr Expr | TProp Prop
instance Show Type where
  show (TExpr e) = show e
  show (TProp p) = show p

data Prop = PExpr Expr
          | Brel Brel Expr Expr
          | And [Prop]
instance Show Prop where
  show (PExpr e) = show e
  show (Brel brel e1 e2) = show e1 ++ " = " ++ show e2
  show (And ps) = intercalate " /\\ " $ map show ps


data Brel = Eq
instance Show Brel where show Eq = "="

data ProofBody = Tactic :> ProofBody | Tactic :| ProofBody | Single Tactic | Empty
               deriving Show

-- data ProofBody = Tactic :> ProofBody | Tactic :| ProofBody | [ProofBody] :>> ProofBody | Empty 


infixr 4 :>
infixr 4 :|

trivial = "smt_trivial"

ple = "ple"

rewrite = "smt_app"

data Tactic = Trivial
            | Ple
            | Rewrite Expr
            | Destruct Expr
            | Induction {indArg :: Id, indVar :: Id, indHyp :: Id}
            | LetTac Id Tactic Tactic
            | Intros [Id]
            | Revert [Id]
instance Show Tactic where
  show Trivial = trivial
  show Ple = ple
  show (Rewrite e) = rewrite ++ " " ++ showAppArg e
  -- TODO generalize destruct
  show (Destruct (Var n)) = "destruct " ++ n ++ " as [| " ++ n ++ " ]"
  show (Induction arg var hyp) = "induction " ++ arg ++ " as [| " ++ unwords [var,hyp] ++ " ]"
  show (LetTac id t1 t2) = "let " ++ filterWeird id ++ " := " ++ addParens (show t1) ++ " in " ++ show t2
  show (Intros ids) = "intros " ++ unwords ids
  show (Revert ids) = "revert " ++ unwords ids

filterWeird :: String -> String
filterWeird = filter (not . flip elem "$#")