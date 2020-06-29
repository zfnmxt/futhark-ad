{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-warn-missing-fields #-}

module Differentiate where

import           Control.Category                          ((>>>))
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Data
import           Data.Functor.Identity
import           Data.List                                 (sortOn, isPrefixOf)
import           Data.Loc
import qualified Data.Map                                  as M
import           Data.Maybe
import           Data.Semigroup
import           Data.Sequence                             (Seq(..), fromList)
import qualified Data.Text                                 as T
import qualified Data.Text.IO                              as T
import           Debug.Trace
import           GHC.IO.Encoding                           (setLocaleEncoding)
import           System.Directory
import           System.Environment                        (getArgs)
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO

import           Futhark.Actions                           (printAction)
import           Futhark.Binder
import qualified Futhark.CodeGen.Backends.SequentialC      as SequentialC
import qualified Futhark.CodeGen.Backends.SequentialPython as SequentialPy
import           Futhark.Compiler                          (newFutharkConfig,
                                                            runCompilerOnProgram)
import           Futhark.Compiler.CLI
import           Futhark.Construct
import           Futhark.MonadFreshNames
import           Futhark.Optimise.CSE
import           Futhark.Optimise.InPlaceLowering
import           Futhark.Pass
import qualified Futhark.Pass.ExplicitAllocations.Seq      as Seq
import           Futhark.Pass.FirstOrderTransform
import           Futhark.Pass.Simplify
import           Futhark.Passes                            (standardPipeline)
import           Futhark.Pipeline
import           Futhark.IR.Primitive
import           Futhark.IR.SeqMem                         (SeqMem)
import           Futhark.IR.SOACS
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)


deriving instance Data BinOp
deriving instance Data Overflow
deriving instance Data IntType
deriving instance Data FloatType

data Adj = Adj VName (Stms SOACS)

data Env = Env
    { adjs :: M.Map VName VName
    , tape :: M.Map VName VName
    , vns :: VNameSource
    }
    
data REnv = REnv
    { tans :: M.Map VName VName
    , envScope :: Scope SOACS
--    , strat :: FwdStrat
    }

--data FwdStrat = Interleave
--              | After
--              | Decoupled
    
data BindEnv = IntEnv IntType Overflow
             | FloatEnv FloatType

defEnv :: BindEnv
defEnv = IntEnv Int32 OverflowWrap
    
type ADBind = ReaderT BindEnv (Binder SOACS)

newtype ADM a = ADM (ReaderT REnv (State Env) a)
  deriving (Functor, Applicative, Monad,
            MonadReader REnv, MonadState Env, MonadFreshNames)

instance MonadFreshNames (State Env) where
  getNameSource = gets vns
  putNameSource vns' = modify (\env -> env { vns = vns' })

instance HasScope SOACS ADM where
  askScope = asks envScope

instance LocalScope SOACS ADM where
  localScope scope = local $ \env -> env { envScope = scope <> envScope env }
  
runADBind :: BindEnv -> ADBind a -> ADM (a, Stms SOACS)
runADBind env m = (runBinder . (flip runReaderT) env) m

runADBind_ :: BindEnv -> ADBind a -> ADM (Stms SOACS)
runADBind_ env m = snd <$> runADBind env m

runADM :: MonadFreshNames m => ADM a -> REnv -> m a
runADM (ADM m) renv =
  modifyNameSource $ \vn -> (\(a, env) -> (a, vns env)) $ runState (runReaderT m renv) (Env mempty mempty vn)

tanVName :: VName -> ADM VName
tanVName v = newVName (baseString v <> "_tan")

adjVName :: VName -> ADM VName
adjVName v = do
  vbar <- newVName (baseString v <> "_adj")
  modify $ \env -> env { adjs = M.insert v vbar (adjs env) }
  env <- get
  return vbar

accVName :: VName -> ADM VName
accVName v = newVName (baseString v <> "_acc")

zeroTan :: Type -> ADM SubExp
zeroTan (Prim t) = return $ constant $ blankPrimValue t

mkConst :: (Integral i) => BindEnv -> i -> SubExp
mkConst (IntEnv it _) = Constant . IntValue . intValue it
mkConst (FloatEnv ft) = Constant . FloatValue . floatValue ft

mkConstM :: (Integral i) => i -> ADBind SubExp
mkConstM i = asks ((flip mkConst) i)

insTape :: VName -> VName -> ADM ()
insTape v acc = modify $ \env -> env { tape = M.insert v acc (tape env) }

mkAdjoint :: (PatElemT Type) -> ADM (Stms SOACS)
mkAdjoint pat@(PatElem p (Prim t)) = do
  p' <- adjVName p
  if "res"  `isPrefixOf` baseString p -- Big yikes, fix!
    then
      let benv = case t of
                   (IntType it)   -> IntEnv it OverflowWrap
                   (FloatType ft) -> FloatEnv ft
      in return mempty --runBinderT'_ $ letBindNames [p'] $ BasicOp $ SubExp $ mkConst benv 1 
    else runBinderT'_ $ letBindNames [p'] (BasicOp (SubExp (constant (blankPrimValue t))))

mkAdjointParam pat@(Param p (Prim t)) = do
  p' <- adjVName p
  runBinderT'_ $ letBindNames [p'] (BasicOp (SubExp (constant (blankPrimValue t))))
   
--insAdjoint :: (PatElemT Type) -> ADBind (Stms SOACS)
--insAdjoint pat@(PatElem p (Prim t)) = do
--   p' <- adjVName p
--   lift $ letBindNames [p'] (BasicOp (SubExp (constant (blankPrimValue t))))
   
lookupAcc :: VName -> ADM (VName)
lookupAcc v = do
  maybeV' <- gets $ M.lookup v . tape
  case maybeV' of
    Nothing -> error "oops"
    Just v' -> return v'

--class AdjBinder a where
--  newAdj :: a -> ADM (VName)
--  addAdj :: VName -> Stms SOACS -> ADM (VName)
--
--instance AdjBinder (PatElemT dec) where
--  newAdj (PatElem p t) = 

class TanBinder a where
  mkTan :: a -> ADM a
  getVNames :: a -> [VName]
  withTans :: [a] -> ([a] -> ADM b) -> ADM b
  withTans as m = do
    as' <- mapM mkTan as
    let f env = env { tans = M.fromList (zip (concatMap getVNames as) (concatMap getVNames as'))
                               `M.union` tans env
                    }
    local f $ m as'
  withTan :: a -> (a -> ADM b) -> ADM b
  withTan a m = withTans [a] $ \[a'] -> m a'

instance TanBinder (PatElemT dec) where
  mkTan (PatElem p t) = do
    p' <- tanVName p
    return $ PatElem p' t
  getVNames (PatElem p t) = [p]

instance TanBinder (Param attr) where
  mkTan (Param p t) = do
    p' <- tanVName p
    return $ Param p' t
  getVNames (Param p t) = [p]

instance (TanBinder a) => TanBinder [a] where
  mkTan = mapM mkTan
  getVNames = concatMap getVNames

data TanStm = TanStm { primalStm :: Stms SOACS
                     , tanStms :: Stms SOACS
                     }
              
class Tangent a where
  type TangentType a :: *
  tangent :: a -> ADM (TangentType a)

instance Tangent VName where
  type TangentType VName = VName
  tangent v = do
    maybeTan <- asks $ M.lookup v . tans
    case maybeTan of
      Just v' -> return v'
      Nothing -> error "Oh no!"
    
instance Tangent SubExp where
  type TangentType SubExp = SubExp
  tangent (Constant c) = zeroTan $ Prim $ primValueType c
  tangent (Var v) = do
    maybeTan <- asks $ M.lookup v . tans
    case maybeTan of
      Just v' -> return $ Var v'
      Nothing -> do t <- lookupType v; zeroTan t

instance Tangent Stm where
  type TangentType Stm = TanStm
  tangent = (flip fwdStm) return

class Adjoint a where
  adjoint :: a -> ADM a
 -- (+=) :: a -> SubExp -> ADBind SubExp -- ADM (Stms SOACS)
  mkBEnv :: a -> ADM (BindEnv)
  insAdj :: a -> VName -> ADM ()

instance Adjoint VName where
  adjoint v = do
   maybeAdj <- gets $ M.lookup v . adjs
   case maybeAdj of
        Just v' -> return v'
        Nothing ->  error $ "oops: " ++ show v
  --(+=) v se = do
  --  maybeV' <- gets $ M.lookup v . adjs
  --  case maybeV' of
  --    Nothing -> error "oops"
  --    Just v' -> do
  --      t <- lookupType v'
  --      let numEnv = case t of
  --           (Prim (IntType it)) -> IntEnv it OverflowWrap
  --           (Prim (FloatType ft)) -> FloatEnv ft
  --      runADBind_ numEnv $ Var v' +^ se
  --(+=) v' se = Var v' +^ se
      
  mkBEnv v = do
    maybeV' <- gets $ M.lookup v . adjs
    case maybeV' of
      Nothing -> error "oops"
      Just v' -> do
        t <- lookupType v'
        let numEnv = case t of
             (Prim (IntType it)) ->   IntEnv it OverflowWrap
             (Prim (FloatType ft)) -> FloatEnv ft
        return numEnv
        
  insAdj v vbar = modify $ \env -> env { tape = M.insert v vbar (adjs env) }

instance Adjoint SubExp where
  adjoint (Constant c) = zeroTan $ Prim $ primValueType c
  adjoint (Var v) = Var <$> adjoint v

  mkBEnv Constant{} = return defEnv
  mkBEnv (Var v)    = mkBEnv v
  
  insAdj Constant{} vbar = return ()
  insAdj (Var v)   vbar = insAdj v vbar
  
instance Adjoint (Param decl) where
  adjoint (Param p t) = do
    pbar <- adjoint p
    return $ Param pbar t

revFwdStm :: Stm -> ADM Stm
revFwdStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (DoLoop [] valPats (ForLoop v it bound []) body)) = do
   ps <- accVName p
   insTape p ps
   let pAcc = PatElem ps (Array t (Shape [bound]) NoUniqueness)
       Body decs stms [res] = body
       updateAcc = BasicOp $ Update ps [DimSlice (Var v) (Constant $ IntValue $ intValue it 1) (Constant $ IntValue $ intValue it 1)] res
   updateAccStms <- runBinderT'_ $ letBind (Pattern [] [pAcc]) updateAcc
   let body' = Body decs (stms <> updateAccStms) [res, Var ps]
   return (Let (Pattern [] [pat, pAcc]) aux (DoLoop [] valPats (ForLoop v it bound []) body'))
   
revFwdStm stm = return stm

doStms :: [ADM (Stms SOACS)] -> ADM (Stms SOACS)
doStms (stmsM:stmsMs) = do
  stms  <- stmsM
  stmss <- doStms stmsMs
  return $ stms <> stmss
doStms [] = return mempty

mkBindEnv :: VName -> ADM BindEnv
mkBindEnv v = do
  t <- lookupType v
  return $ case t of
    (Prim (IntType it)) -> IntEnv it OverflowWrap
    (Prim (FloatType ft)) -> FloatEnv ft

getVar :: SubExp -> VName
getVar (Var v) = v

exts (Prim t) = Prim t
exts (Mem s) = Mem s
exts _ = error "oops"

revStm :: Stm -> ADM (Stms SOACS, Stms SOACS)
revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (BasicOp (SubExp se))) = do
  s1 <- mkAdjoint pat
  pbar <- adjoint p
  sebar <- adjoint se
  benv <- mkBEnv se
  (sebar', s2) <- runADBind benv $ getVar <$> (sebar +^ Var pbar)
  insAdj se sebar'
  return (s2, s1)

revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (BasicOp (UnOp op se))) = do
  s1 <- mkAdjoint pat
  return (mempty, s1)

revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (DoLoop [] [(accP@(Param acc acct), (Var x))] (ForLoop v it bound []) body@(Body decs stms [res]))) = do
  s1 <- mkAdjoint pat
  p_bar <- adjoint p
  ps <- lookupAcc p
  resetAccBar <- mkAdjointParam accP
  accP_bar <- adjoint accP
  x_bar <- adjoint x
  x_t <- lookupType x
  --let valPats' = [(Param acc acct, Constant $ IntValue $ intValue it 1), (Param x_bar (toDecl x_t Nonunique), Var x_bar)]
  let valPats' = [(accP_bar, Constant $ IntValue $ intValue it 1)]
      currAcc   = Index ps [DimSlice (Var v) (Constant $ IntValue $ intValue it 1) (Constant $ IntValue $ intValue it 1)]
  bindAcc <- runBinderT'_ $ letBind (Pattern [] [PatElem acc (fromDecl acct)]) (BasicOp currAcc)
  (stms', initAdjs) <- revStms stms
  res_bar <- adjoint res
  let body' = Body decs (initAdjs <> bindAcc <> stms') [res_bar]
  return $ (oneStm (Let (Pattern [] [PatElem p_bar (Prim t)]) aux (DoLoop [] valPats' (ForLoop v it bound []) body')), s1 <> resetAccBar)

revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux cOp@(BasicOp CmpOp{})) = do
  s1 <- mkAdjoint pat
  return (mempty, s1)

revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (BasicOp (BinOp op x y))) = do
  s1 <- mkAdjoint pat
  pbar <- adjoint p
  xbar <- adjoint x
  ybar <- adjoint y
  case op of
    op | op' `elem` ["Add", "FAdd"] -> do
         (xbar', s2) <- runADBind (bindEnv op) $ getVar <$> xbar +^ Var pbar
         (ybar', s3) <- runADBind (bindEnv op) $ getVar <$> ybar +^ Var pbar
         insAdj x xbar'
         insAdj y ybar'
         return $ (s2 <> s3, s1)

    op | op' `elem` ["Sub", "FSub"] -> do
         (ybar', s2) <- runADBind (bindEnv op) $ getVar <$> (do y0 <- mkConstM 0; y1 <- y0 -^ Var pbar; ybar +^ y1)
         (xbar', s3) <- runADBind (bindEnv op) $ getVar <$> xbar +^ Var pbar
         insAdj x xbar'
         insAdj y ybar'
         return $ (s2 <> s3, s1)

    op | op' `elem` ["Mul", "FMul"] -> do
         (xbar', s2) <- runADBind (bindEnv op) $ getVar <$> (do x0 <- (Var pbar) *^ y; xbar +^ x0)
         (ybar', s3) <- runADBind (bindEnv op) $ getVar <$> (do y0 <- (Var pbar) *^ x; xbar +^ y0)
         insAdj x xbar'
         insAdj y ybar'
         return $ (s2 <> s3, s1)
----    op | op' `elem` ["UDiv", "SDiv", "FDiv"] ->
----      runADBind_ (bindEnv op) $ do
----        x1 <- x' *^ y
----        x2 <- x *^ y'
----        x3 <- x1 -^ x2
----        x4 <- y *^ y
----        x5 <- x3 //^ x4
----        bindTans pes' x5
----        
----    op | op' `elem` ["Pow", "FPow"] ->
----       runADBind_ (bindEnv op) $ do
----         x0 <- mkConstM 1
----         x1 <- y -^ x0         -- x1 = y - 1
----         x2 <- x **^ x1        -- x2 = x^x1 = x^{y - 1}
----         x3 <- y *^ x2         -- x3 = y x^{y-1} = y x2
----         x4 <- x3 *^ x'        -- x4 = y f^{y-1} x' = x3 x'
----         x5 <- "log32" $^ x    -- x5 = log (x)  Probably should intelligently select log32 or log64
----         x6 <- x **^y          -- x6 = x^y
----         x7 <- x6 *^ x5        -- x7 = x^y ln (x) = x6 x5
----         x8 <- x7 *^ y'        -- x8 = x^y ln(x) y' = x7 y'
----         x9 <- x4 +^ x8        -- x9 = x x^{y - 1} x' + x^y ln(x) y'
----         bindTans pes' x9
----  m $ TanStm (oneStm stm) stms
  where op' = showConstr $ toConstr op

revStm stm = error $ "unsupported stm: " ++ pretty stm ++ "\n\n\n" ++ show stm

revStms :: Stms SOACS -> ADM (Stms SOACS, Stms SOACS)
revStms (stm :<| stms) =
 do
  revFwdStm stm
  (stm', initAdj) <- revStm stm
  (stms', initAdjs) <-revStms stms
  return (stm' <> stms', initAdj <> initAdjs)
revStms mempty = return (mempty, mempty)

-- TODO: fix
revBody :: Body -> ADM Body
revBody b@(Body desc stms res) = do
  (stms', adjInits) <- revStms stms
  return $ Body desc (adjInits <> stms') res

($^) :: String -> SubExp -> ADBind SubExp
($^) f x = lift $ letSubExp "f x" $ Apply (nameFromString f) [(x, Observe)] [primRetType rt] (Safe, noLoc, mempty)
  where Just (_, rt, _) = M.lookup f primFuns

(+^) :: SubExp -> SubExp -> ADBind SubExp
(+^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Add it ovf
             FloatEnv ft -> FAdd ft
  lift $ letSubExp "+^" $ BasicOp (BinOp op x y)
  
(-^) :: SubExp -> SubExp -> ADBind SubExp
(-^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Sub it ovf
             FloatEnv ft -> FSub ft
  lift $ letSubExp "-^" $ BasicOp (BinOp op x y)

(*^) :: SubExp -> SubExp -> ADBind SubExp
(*^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Mul it ovf
             FloatEnv ft -> FMul ft
  lift $ letSubExp "*^" $ BasicOp (BinOp op x y)
      
(//^) :: SubExp -> SubExp -> ADBind SubExp
(//^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it _ -> SDiv it
             FloatEnv ft -> FDiv ft
  lift $ letSubExp "//^" $ BasicOp (BinOp op x y)

(**^) :: SubExp -> SubExp -> ADBind SubExp
(**^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it _ -> Pow it
             FloatEnv ft -> FPow ft
  lift $ letSubExp "**^" $ BasicOp (BinOp op x y)

bindTans :: [PatElem] -> SubExp -> ADBind ()
bindTans pes' se = do
  e <- lift $ eSubExp se
  lift $ letBindNames (map patElemName pes') e

bindEnv :: BinOp -> BindEnv
bindEnv (Add it ovf) = IntEnv it ovf
bindEnv (FAdd ft)    = FloatEnv ft
bindEnv (Sub it ovf) = IntEnv it ovf
bindEnv (FSub ft)    = FloatEnv ft
bindEnv (Mul it ovf) = IntEnv it ovf
bindEnv (FMul ft)    = FloatEnv ft
bindEnv (UDiv it)    = IntEnv it OverflowWrap
bindEnv (SDiv it)    = IntEnv it OverflowWrap
bindEnv (FDiv ft)    = FloatEnv ft
bindEnv (Pow it)     = IntEnv it OverflowWrap
bindEnv (FPow ft)    = FloatEnv ft

fwdStm :: Stm -> (TanStm -> ADM a) -> ADM a
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (SubExp se))) m = do
  se' <- tangent se
  withTans pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (SubExp se'))))
    
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (Opaque se))) m = do
  se' <- tangent se
  withTans pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (Opaque se'))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ArrayLit ses t))) m = do
  ses' <- mapM tangent ses
  traceM $ pretty stm
  withTans pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (ArrayLit ses' t))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (UnOp op x))) m = do
  x' <- tangent x
  withTans pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (UnOp op x'))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (BinOp op x y))) m = do
  x' <- tangent x
  y' <- tangent y
  withTans pes $ \pes' -> do
    stms <- case op of
      op | op' `elem` ["Add", "FAdd"] ->
        runADBind_ (bindEnv op)  $ do
          x1 <- x' +^ y'
          bindTans pes' x1

      op | op' `elem` ["Sub", "FSub"] -> 
        runADBind_ (bindEnv op) $ do
          x1 <- x' -^ y'
          bindTans pes' x1

      op | op' `elem` ["Mul", "FMul"] ->
        runADBind_ (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 +^ x2
          bindTans pes' x3

      op | op' `elem` ["UDiv", "SDiv", "FDiv"] ->
        runADBind_ (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 -^ x2
          x4 <- y *^ y
          x5 <- x3 //^ x4
          bindTans pes' x5
          
      op | op' `elem` ["Pow", "FPow"] ->
         runADBind_ (bindEnv op) $ do
           x0 <- mkConstM 1
           x1 <- y -^ x0         -- x1 = y - 1
           x2 <- x **^ x1        -- x2 = x^x1 = x^{y - 1}
           x3 <- y *^ x2         -- x3 = y x^{y-1} = y x2
           x4 <- x3 *^ x'        -- x4 = y f^{y-1} x' = x3 x'
           x5 <- "log32" $^ x    -- x5 = log (x)  Probably should intelligently select log32 or log64
           x6 <- x **^y          -- x6 = x^y
           x7 <- x6 *^ x5        -- x7 = x^y ln (x) = x6 x5
           x8 <- x7 *^ y'        -- x8 = x^y ln(x) y' = x7 y'
           x9 <- x4 +^ x8        -- x9 = x x^{y - 1} x' + x^y ln(x) y'
           bindTans pes' x9
    m $ TanStm (oneStm stm) stms
    where op' = showConstr $ toConstr op
   
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ConvOp op x))) m = do
  x' <- tangent x
  withTan pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (BasicOp (ConvOp op x'))))

fwdStm stm@(Let (Pattern [] pes) aux assert@(BasicOp (Assert x err (loc, locs)))) m =
  withTan pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux assert))

fwdStm stm@(Let (Pattern [] pes) aux cOp@(BasicOp CmpOp{})) m =
  withTan pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux cOp))

fwdStm stm@(Let (Pattern [] pes) aux (If cond t f attr)) m = do
  t' <- fwdBodyInterleave' t
  f' <- fwdBodyInterleave' f
  withTan pes $ \pes' ->
    m $
    TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (If cond t' f' attr)))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    body' <- fwdBodyInterleave' body
    withTans pes $ \pes' ->
      m $
      TanStm mempty (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body')))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter' body
    withTans pes $ \pes' ->
      m $
      TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop v it bound []) body')))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop i it bound loop_vars) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' ->
    withTans (map fst loop_vars) $ \loopParams' -> do
      let f p n = do n' <- tangent n; return (p, n')
      loop_vars' <- zipWithM f loopParams' (map snd loop_vars)
      (_, body') <- fwdBodyAfter' body
      withTans pes $ \pes' ->
        m $
        TanStm (oneStm stm) (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop i it bound (loop_vars ++ loop_vars')) body')))

fwdStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

fwdStms :: (Monoid a) => (TanStm -> a) -> Stms SOACS -> ADM a -> ADM a
fwdStms f (stm :<| stms) m =
  fwdStm stm $ \stm' -> do
    as <- fwdStms f stms m
    return $ f stm' <> as
fwdStms _ Empty m = m

fwdStmsInterleave :: Stms SOACS -> ADM (Stms SOACS) -> ADM (Stms SOACS)
fwdStmsInterleave = fwdStms f
  where f tStm = primalStm tStm <> tanStms tStm

fwdStmsAfter :: Stms SOACS -> ADM (Stms SOACS, Stms SOACS) -> ADM (Stms SOACS, Stms SOACS)
fwdStmsAfter = fwdStms f
  where f tStm = (primalStm tStm, tanStms tStm)

fwdBodyInterleave :: Stms SOACS -> ADM Body -> ADM Body
fwdBodyInterleave stms m =
  case stms of
    (stm :<| stms') ->
      fwdStm stm $ \tStm -> do
        Body _ stms'' res <- fwdBodyInterleave stms' m
        return $ mkBody (primalStm tStm <> tanStms tStm <> stms'') res
    Empty -> m

fwdBodyInterleave' :: Body -> ADM Body
fwdBodyInterleave' (Body _ stms res) =
  fwdBodyInterleave stms $ do
    res' <- mapM tangent res
    return $ mkBody mempty $ res ++ res'

fwdBodyAfter :: Stms SOACS -> ADM (Body, Body) -> ADM (Body, Body)
fwdBodyAfter stms m =
  case stms of
    (stm :<| stms') ->
      fwdStm stm $ \tStm -> do
        (Body _ stms1 res1, Body _ stms2 res2) <- fwdBodyAfter stms' m
        return $ (mkBody (primalStm tStm <> stms1) res1, mkBody ((tanStms tStm) <> stms2) res2)
    Empty -> m

fwdBodyAfter' :: Body -> ADM (Body, Body)
fwdBodyAfter' (Body _ stms res) = do
  fwdBodyAfter stms $ do
    res' <- mapM tangent res
    return $ (mkBody mempty res, mkBody mempty res')
  
fwdFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
fwdFun consts fundef = do
  let initial_renv = REnv { tans = mempty, envScope = mempty }
  flip runADM initial_renv $ inScopeOf consts $
    withTan (funDefParams fundef) $ \params' -> do
    body' <- fwdBodyInterleave' $ funDefBody fundef
    return fundef { funDefParams = funDefParams fundef ++ params'
                  , funDefBody = body'
                  , funDefRetType = funDefRetType fundef ++ funDefRetType fundef
                  , funDefEntryPoint = (\(a, r) -> (a ++ a, r ++ r)) <$> (funDefEntryPoint fundef)
                  }

fwdPass :: Pass SOACS SOACS
fwdPass =
  Pass { passName = "automatic differenation"
       , passDescription = "apply automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure fwdFun
       }

revFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
revFun consts fundef = do
  let initial_renv = REnv { tans = mempty, envScope = mempty }
  flip runADM initial_renv $ inScopeOf consts $ inScopeOf fundef $ do
    let params = funDefParams fundef
        ret = map (\(Param _ t) -> exts t) params
    paramAdjoints <- foldM (\stms p -> do stms' <- mkAdjointParam p; return (stms' <> stms)) mempty params
    let (Body _ st res) = funDefBody fundef
    (Body attr stms _) <- revBody $ funDefBody fundef
    resAdjs <- inScopeOf st $ mapM (\(Var v) -> do t <- lookupType v; v' <- adjoint v; return $ Param v' (toDecl t Nonunique)) res
    res' <- mapM (\(Param p _) -> Var <$> adjoint p) $ funDefParams fundef
    error $ pretty $ fundef { funDefParams = funDefParams fundef ++ resAdjs
                    , funDefBody = Body attr (paramAdjoints <> stms) res'
                    , funDefRetType = ret --funDefRetType fundef -- concatMap (replicate (length params + 0)) $ funDefRetType fundef -- ridiculous, fix
                    , funDefEntryPoint = (\(a, r) -> (a, concat (replicate (length params + 1) r))) <$> (funDefEntryPoint fundef)
                    }
 where --exts (Array t (Shape i) u) ty =
           --let benv = case ty of
           --             (IntType it)   -> IntEnv it OverflowWrap
           --             (FloatType ft) -> FloatEnv ft
           --    ses = map (Ext . mkConst benv) i
           --in Array t (Shape ses) u
      
revPass :: Pass SOACS SOACS
revPass =
  Pass { passName = "reverse automatic differentiation"
       , passDescription = "apply reverse automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure revFun
       }
