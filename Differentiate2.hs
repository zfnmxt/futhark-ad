{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-missing-fields #-}

module Differentiate2 () where

import           Control.Category                          ((>>>))
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State
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
  
runADBind :: BindEnv -> ADBind a -> ADM (Stms SOACS)
runADBind env m = (runBinder_ . (flip runReaderT) env) m

runADM :: MonadFreshNames m => ADM a -> REnv -> m a
runADM (ADM m) renv =
  modifyNameSource $ \vn -> (\(a, env) -> (a, vns env)) $ runState (runReaderT m renv) (Env mempty mempty vn)

tanVName :: VName -> ADM VName
tanVName v = newVName (baseString v <> "_tan")

adjVName :: VName -> ADM VName
adjVName v = newVName (baseString v <> "_adj")

accVName :: VName -> ADM VName
accVName v = newVName (baseString v <> "_acc")

zeroTan :: Type -> ADM SubExp
zeroTan (Prim t) = return $ constant $ blankPrimValue t

mkConst :: (Integral i) => BindEnv -> i -> SubExp
mkConst (IntEnv it _) = Constant . IntValue . intValue it
mkConst (FloatEnv ft) = Constant . FloatValue . floatValue ft

mkConstM :: (Integral i) => i -> ADBind SubExp
mkConstM i = asks ((flip mkConst) i)

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
    local f $ m as
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

data TanStm = TanStm { primalStm :: Stm
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
  tangent (Var v) = Var <$> tangent v

instance Tangent Stm where
  type TangentType Stm = TanStm
  tangent = (flip fwdStm) return

instance Tangent (Stms SOACS) where
  type TangentType (Stms SOACS) = [TanStm]
  tangent = fwdStms pure

class Adjoint a where
  type AdjointType a :: *
  adjoint :: a -> ADM (AdjointType a)

instance Adjoint SubExp where
  type AdjointType SubExp = SubExp
  adjoint (Constant c) = zeroTan $ Prim $ primValueType c
  adjoint (Var v) = do
    maybeAdj <- gets $ M.lookup v . adjs
    case maybeAdj of
      Just v' -> return $ Var v'
      Nothing -> error "Oh no!"

--instance Adjoint Stm where
--  type AdjointType Stm = Stms SOACS
--  adjoint = revStm
--

revFwdStm :: Stm -> ADM Stm
revFwdStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (DoLoop [] valPats (ForLoop v it bound []) body)) = do
   ps <- accVName p
   let pAcc = PatElem ps (Array t (Shape [bound]) NoUniqueness)
       Body decs stms [res] = body
       updateAcc = BasicOp $ Update ps [DimSlice (Var v) (Constant $ IntValue $ intValue it 1) (Constant $ IntValue $ intValue it 1)] res
   updateAccStms <- runBinderT'_ $ letBind (Pattern [] [pAcc]) updateAcc
   let body' = Body decs (stms <> updateAccStms) [res, Var ps]
   return (Let (Pattern [] [pat, pAcc]) aux (DoLoop [] valPats (ForLoop v it bound []) body'))

--fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
--  let (valParams, vals) = unzip valPats
--  vals' <- mapM tangent vals
--  withTans valParams $ \valParams' -> do
--    (_, body') <- fwdBodyAfter body
--    withTans pes $ \pes' ->
--      m $
--      TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop v it bound []) body')))

($^) :: String -> SubExp -> ADBind SubExp
($^) f x = lift $ letSubExp "f x" $ Apply (nameFromString f) [(x, Observe)] [primRetType rt] (Safe, noLoc, mempty)
  where Just (_, rt, _) = M.lookup f primFuns

(+^) :: SubExp -> SubExp -> ADBind SubExp
(+^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Add it ovf
             FloatEnv ft -> FAdd ft
  lift $ letSubExp (pretty x ++ "+^" ++ pretty y) $ BasicOp (BinOp op x y)
  
(-^) :: SubExp -> SubExp -> ADBind SubExp
(-^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Sub it ovf
             FloatEnv ft -> FSub ft
  lift $ letSubExp (pretty x ++ "-^" ++ pretty y) $ BasicOp (BinOp op x y)

(*^) :: SubExp -> SubExp -> ADBind SubExp
(*^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it ovf -> Mul it ovf
             FloatEnv ft -> FMul ft
  lift $ letSubExp (pretty x ++ "*^" ++ pretty y) $ BasicOp (BinOp op x y)
      
(//^) :: SubExp -> SubExp -> ADBind SubExp
(//^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it _ -> SDiv it
             FloatEnv ft -> FDiv ft
  lift $ letSubExp (pretty x ++ "//^" ++ pretty y) $ BasicOp (BinOp op x y)

(**^) :: SubExp -> SubExp -> ADBind SubExp
(**^) x y = do
  numEnv <- ask
  let op = case numEnv of
             IntEnv it _ -> Pow it
             FloatEnv ft -> FPow ft
  lift $ letSubExp (pretty x ++ "**^" ++ pretty y) $ BasicOp (BinOp op x y)

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
    TanStm stm (oneStm (Let (Pattern [] pes') aux (BasicOp (SubExp se'))))
    
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (Opaque se))) m = do
  se' <- tangent se
  withTans pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (BasicOp (Opaque se'))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ArrayLit ses t))) m = do
  ses' <- mapM tangent ses
  traceM $ pretty stm
  withTans pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (BasicOp (ArrayLit ses' t))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (UnOp op x))) m = do
  x' <- tangent x
  withTans pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (BasicOp (UnOp op x'))))

fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (BinOp op x y))) m = do
  x' <- tangent x
  y' <- tangent y
  withTans pes $ \pes' -> do
    stms <- case op of
      op |  op `elem` [Add{}, FAdd{}] ->
        runADBind (bindEnv op)  $ do
          x1 <- x' +^ y'
          bindTans pes' x1

      op | op `elem` [Sub{}, FSub{}] -> 
        runADBind (bindEnv op) $ do
          x1 <- x' -^ y'
          bindTans pes' x1

      op | op `elem` [Mul{}, FMul{}] ->
        runADBind (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 +^ x2
          bindTans pes' x3

      op | op `elem` [UDiv{}, SDiv{}, FDiv{}] ->
        runADBind (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 -^ x2
          x4 <- y *^ y
          x5 <- x3 //^ x4
          bindTans pes' x5
          
      op | op `elem` [Pow{}, FPow{}] ->
         runADBind (bindEnv op) $ do
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
    m $ TanStm stm stms
   
fwdStm stm@(Let (Pattern [] pes) aux (BasicOp (ConvOp op x))) m = do
  x' <- tangent x
  withTan pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (BasicOp (ConvOp op x'))))

fwdStm stm@(Let (Pattern [] pes) aux assert@(BasicOp (Assert x err (loc, locs)))) m =
  withTan pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux assert))

fwdStm stm@(Let (Pattern [] pes) aux cOp@(BasicOp CmpOp{})) m =
  withTan pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux cOp))

fwdStm stm@(Let (Pattern [] pes) aux (If cond t f attr)) m = do
  t' <- fwdBodyInterleave t
  f' <- fwdBodyInterleave f
  withTan pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (If cond t' f' attr)))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter body
    withTans pes $ \pes' ->
      m $
      TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body')))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter body
    withTans pes $ \pes' ->
      m $
      TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop v it bound []) body')))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop i it bound loop_vars) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' ->
    withTans (map fst loop_vars) $ \loopParams' -> do
      let f p n = do n' <- tangent n; return (p, n')
      loop_vars' <- zipWithM f loopParams' (map snd loop_vars)
      (_, body') <- fwdBodyAfter body
      withTans pes $ \pes' ->
        m $
        TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop i it bound (loop_vars ++ loop_vars')) body')))

fwdStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

fwdStms :: (Monoid a) => (TanStm -> a) -> Stms SOACS -> ADM a
fwdStms f (stm :<| stms) =
  fwdStm stm $ \stm' -> do
    as <- fwdStms f stms
    return $ f stm' <> as
fwdStms _ Empty = return mempty

fwdStmsInterleave :: Stms SOACS -> ADM (Stms SOACS)
fwdStmsInterleave = fwdStms f
  where f tStm = oneStm (primalStm tStm) <> tanStms tStm

fwdStmsAfter :: Stms SOACS -> ADM (Stms SOACS, Stms SOACS)
fwdStmsAfter = fwdStms f
  where f tStm = (oneStm (primalStm tStm), tanStms tStm)

fwdStmsAfter_ :: Stms SOACS -> ADM (Stms SOACS)
fwdStmsAfter_ = ((\(p, t) -> p <> t) <$>) . fwdStmsAfter

fwdBody :: (Stms SOACS -> ADM (Stms SOACS)) -> Body -> ADM Body
fwdBody f (Body _ stms res) = do
  stms' <- f stms
  res'  <- mapM tangent res
  return $ mkBody stms' $ res ++ res'

fwdBodyInterleave :: Body -> ADM Body
fwdBodyInterleave = fwdBody fwdStmsInterleave

fwdBodyAfter :: Body -> ADM (Body, Body)
fwdBodyAfter body@(Body _ stms res) = do
  stms' <- snd <$> fwdStmsAfter stms
  res'  <- mapM tangent res
  return $ (body, mkBody stms' res')
  
