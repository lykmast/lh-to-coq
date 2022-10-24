module Coq where
import Data.List (intercalate)
type Id = String

data Def = Def {getDefId :: Id, getDefExpr :: Expr}

instance Show Def where
  show (Def id expr) = "Definition " ++ id ++ " := " ++ show expr

data Expr = Fun Id Expr
          | App Expr Expr
          | Var Id
          | Match Expr Id [(Pat, Expr)]
          | Let Id Expr Expr

data Pat = Pat Id [Id]
 
instance Show Pat where
  show (Pat c args) = c ++ " " ++ unwords args
  
addParens :: String -> String
addParens = (++ ")") . ("(" ++)

parenShow :: Show a => a -> String
parenShow = addParens . show

instance Show Expr where
  show (Var id)   = id
  show (Fun id e) = addParens $ "fun " ++ id ++ " => " ++ show e
  show (App f x)  = addParens $ show f ++ " " ++ show x
  show (Let id b e) = "let " ++ id ++ " := " ++ show b ++ " in " ++ show e
  show (Match e id branches)
    = let showBranch (p, e) = "| " ++ show p ++ " => " ++ show e
      in  addParens $ "match " ++ show e ++ " as " ++ id ++ "\n" ++ intercalate "\n" (map showBranch branches)