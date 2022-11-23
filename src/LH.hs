module LH where

import qualified Coq as C

import qualified Data.Map as M
import Control.Monad.Reader
import Data.List(findIndex)
import Util
import qualified Data.Bifunctor as B

data Proof = Proof Def Signature deriving Show
data Def = Def {defName :: Id, defArgs:: [Id], defBody :: Expr} deriving Show
data Expr = App Id [Expr]
          | Var Id
          | QMark Expr Expr
          | Unit
          | Case Expr Id [(Pat, Expr)]
          | Let Id Expr Expr
          deriving Show

data Type = TVar Id | TDat Id [Type] deriving Show

data ProofBody = PCase Id [(Pat, ProofBody)]
               | PCall Id [Expr]
               | IndCase Id [(Pat,ProofBody)]
               | IndCall Id [Expr]
               | PUnit

isProof :: Signature -> Bool
isProof = (== "()") . typeName . lhArgType . sigRes
  where
    typeName :: Type -> String
    typeName (TVar n) = n
    typeName (TDat n _) = n

data Pat = Pat {patCon :: Id, patArgs :: [Id]} deriving Show

data LHExpr = And [LHExpr]
            | Brel Brel LHExpr LHExpr
            | LHApp Id [LHExpr]
            | LHVar Id
            deriving Show

data Brel = Eq deriving Show

data LHArg = LHArg { lhArgName :: Id, lhArgType :: Type, lhArgReft :: LHExpr} deriving Show
data Signature = Signature {sigArgs :: [LHArg], sigRes :: LHArg} deriving Show

renameSigArgs :: [Id] -> Signature -> Signature
renameSigArgs args (Signature sArgs res) =
    Signature (map runRename sArgs) (runRename res)
  where
    renames = M.fromList $ zip (map lhArgName sArgs) args
    runRename = flip runReader renames . renameArg


renameArg :: LHArg -> Reader Renames LHArg
renameArg (LHArg name t reft) = LHArg <$> rename name <*> pure t <*> renameReft reft


type Renames = M.Map Id Id

renameReft :: LHExpr -> Reader Renames LHExpr
renameReft (And es)       = And    <$> mapM renameReft es
renameReft (Brel b e1 e2) = Brel b <$> renameReft e1 <*> renameReft e2
renameReft (LHApp id es)  = LHApp  <$> rename id <*> mapM renameReft es
renameReft (LHVar id)     = LHVar  <$> rename id

rename :: Id -> Reader Renames Id
rename name = ask <&> (fromMaybe name . M.lookup name)


transLH :: Proof -> C.Proof
transLH (Proof def@(Def name dArgs body) sig) =
  C.Proof name (concatMap transLHArg sigArgs) (transResLHArg res) (transformTop def)
  where Signature sigArgs res = renameSigArgs dArgs sig

transLHArg :: LHArg -> [(Id, C.Type)]
transLHArg (LHArg name ty reft) =
  (name, C.TExpr $ transType ty):
  case reft of
    LHVar "True" -> []
    _            -> [(name ++ "_reft", C.TProp $ transProp reft)]

transResLHArg :: LHArg -> C.Prop
transResLHArg (LHArg _ _ reft) = transProp reft

transType :: Type -> C.Expr
transType (TVar tv) = C.Var tv
transType (TDat con tys) = C.App con $ map transType tys

transPat :: Pat -> C.Pat
transPat (Pat con args) = C.Pat con args

transExpr :: Expr -> C.Expr
transExpr (App f es) = C.App f $ map transExpr es
transExpr (Var x)    = C.Var x
transExpr (Let id e1 e2) = C.Let id (transExpr e1) (transExpr e2)
transExpr (Case e b bs) = C.Match (transExpr e) b $ map (B.bimap transPat transExpr) bs
transExpr Unit = C.Var "()"
transExpr (QMark e1 e2) = C.App "(?)" $ map transExpr [e1,e2]

transProof :: Expr -> [C.Tactic]
transProof (Var x) = [C.Apply (C.Var x)]
transProof (App f es) = [C.Apply (C.App f (map transExpr es))]
transProof (QMark e1 e2) = concatMap transProof [e1,e2]
transProof Unit = [C.Trivial]
transProof (Let id e1 e2) = [C.LetTac id (head $ transProof e1) (head $ transProof e2)]
transProof (Case e _ bs)   = C.Destruct (transExpr e) : concatMap (\(_,e) -> transProof e) bs



transBrel :: Brel -> C.Brel
transBrel Eq = C.Eq

transLHExpr :: LHExpr -> C.Expr
transLHExpr (LHApp f es) = C.App f $ map transLHExpr es
transLHExpr (LHVar x)    = C.Var x
transLHExpr e            = error "not an expression."

transProp :: LHExpr -> C.Prop
transProp (Brel brel e1 e2) = C.Brel (transBrel brel) (transLHExpr e1) (transLHExpr e2)
transProp (And es) = C.And $ map transProp es
transProp (LHApp f es) = C.PExpr $ C.App f $ map transLHExpr es
transProp (LHVar x)    = C.PExpr $ C.Var x

data Environment =  Env
  { envName :: Id
  , envArgs :: M.Map Id Int
  , envIndVars :: M.Map Id Int
  } deriving Show

addInd :: Id -> Int -> Environment -> Environment
addInd ind argPos env = env {envIndVars = M.insert ind argPos (envIndVars env)}

askIds :: Reader Environment (M.Map Id Int)
askIds = asks envArgs

checkInductiveCall :: M.Map Id Int -> [(Expr, Int)] -> Maybe Arg
checkInductiveCall _ [] = Nothing
checkInductiveCall indVars allArgs@((Var arg,pos):args) =
  case M.lookup arg indVars of
    Just x | x == pos -> Just (pos,arg)
    _                 -> checkInductiveCall indVars args
checkInductiveCall indVars (_:args) = checkInductiveCall indVars args

transformTop :: Def -> [C.Tactic]
transformTop def@(Def name args e) =
    case runReader (transformInductive e) env of
      Nothing       -> transBranch e
      Just (arg, e') -> transIndDef (Def name args e') arg
  where
    env = Env name (M.fromList $ zip args [0..]) M.empty

type Arg = (Int,Id)
transformInductive :: Expr -> Reader Environment (Maybe (Arg,Expr))
transformInductive (Let x e1 e2) = do
    ind1 <- transformInductive e1
    ind2 <- transformInductive e2
    return $ case ind1 of
                Nothing       -> fmap (Let x e1) <$> ind2
                Just (ind, e) -> Just (ind, Let x e e2)
transformInductive (Case (Var matchId) ident branches) = do
    Env{envName=name, envArgs=args} <- ask
    let n = fromMaybe (error "Non-existent id.") (M.lookup matchId args)
    mInds <- forM branches $ \(Pat con args, e) ->
                case args of
                  []    -> return Nothing
                  (x:_) -> local (addInd x n) (transformInductive e)
    let
      mIdx                = findIndex isJust mInds
      (mIndArg, mIndExpr) = unzipMaybe $ fromJust . (mInds !!) <$> mIdx
      mBranches           = modifyAt branches <$> mIdx <*>
          pure (replaceExprWith (fromJust mIndExpr))
    return $ (,) <$> mIndArg <*> (Case (Var matchId) ident <$> mBranches)
  where
    replaceExprWith :: Expr -> (Pat, Expr) -> (Pat,Expr)
    replaceExprWith e' (pat,e) = (pat,e')
transformInductive app@(App f args) = do
    Env{envName=name, envIndVars=indVars} <- ask
    indFromArgs <- mapM transformInductive args
    let indFromApp = checkInductiveCall indVars (zip args [0..])
    return $
      if f == name then
        fmap (\arg@(pos,_) -> (arg, App f (deleteAt args pos))) indFromApp
      else
        let modifyArg ix = B.second (setAt args ix) . fromJust $ indFromArgs!!ix
        in  fmap (App f) . modifyArg <$> findIndex isJust indFromArgs
transformInductive t = return Nothing

transIndDef :: Def -> Arg -> [C.Tactic]
transIndDef (Def name args (Case (Var ind) _ [(_,e1), (_,e2)])) (pos, var)
  | null nonIndArgs = induction : transBranch e1 ++ transBranch e2
  | otherwise       = revert : induction : intros : transBranch e1
                        ++ intros : transBranch e2
  where
    revert = C.Revert nonIndArgs
    intros = C.Intros nonIndArgs
    nonIndArgs = deleteAt args pos
    induction = C.Induction (args !! pos) var name
transIndDef def _ = error $ "unhandled proof case of " ++ show def

transBranch :: Expr -> [C.Tactic]
transBranch = updateLast C.toSolve . transProof


transDef :: Def -> C.Def
transDef (Def name args body) = C.Def name args (transExpr body)