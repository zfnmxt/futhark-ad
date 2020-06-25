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

insTape :: VName -> VName -> ADM ()
insTape v acc = modify $ \env -> env { tape = M.insert v acc (tape env) }

insAdjoint :: (PatElemT Type) -> ADM (Stms SOACS)
insAdjoint pat@(PatElem p (Prim t)) = do
   p' <- adjVName p
   runBinderT'_ $ letBindNames [p'] (BasicOp (SubExp (constant (blankPrimValue t))))
   
updateAdj :: VName -> SubExp -> ADM (Stms SOACS)
updateAdj v se = do
  maybeV' <- gets $ M.lookup v . adjs
  case maybeV' of
    Nothing -> error "oops"
    Just v' -> do
      t <- lookupType v'
      let numEnv = case t of
           (Prim (IntType it)) -> IntEnv it OverflowWrap
           (Prim (FloatType ft)) -> FloatEnv ft
      runADBind numEnv $ Var v' +^ se

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
  tangent (Var v) = do
    maybeTan <- asks $ M.lookup v . tans
    case maybeTan of
      Just v' -> return $ Var v'
      Nothing -> do t <- lookupType v; zeroTan t

instance Tangent Stm where
  type TangentType Stm = TanStm
  tangent = (flip fwdStm) return

--instance Tangent (Stms SOACS) where
--  type TangentType (Stms SOACS) = [TanStm]
--  tangent = fwdStms pure

class Adjoint a where
  type AdjointType a :: *
  adjoint :: a -> ADM (AdjointType a)

instance Adjoint VName where
  type AdjointType VName = VName
  adjoint v = do
   maybeAdj <- gets $ M.lookup v . adjs
   case maybeAdj of
        Just v' -> return v'
        Nothing -> error "oops" 

instance Adjoint SubExp where
  type AdjointType SubExp = SubExp
  adjoint (Constant c) = zeroTan $ Prim $ primValueType c
  adjoint (Var v) = Var <$> adjoint v

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

mkBindEnv :: VName -> ADM BindEnv
mkBindEnv v = do
  t <- lookupType v
  return $ case t of
    (Prim (IntType it)) -> IntEnv it OverflowWrap
    (Prim (FloatType ft)) -> FloatEnv ft

revStm :: Stm -> ADM (Stms SOACS)
revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (BasicOp (SubExp se))) = do
  se' <- adjoint se
  stms <- insAdjoint pat
  p' <- adjoint p
  case se' of
    (Var v') -> do
      bEnv <- mkBindEnv v'
      runADBind bEnv $ (Var p') *^ (Var v')
    Constant{} -> return $ mempty
    
revStm stm@(Let (Pattern [] [pat@(PatElem p (Prim t))]) aux (DoLoop [] valPats (ForLoop v it bound []) body)) = do
  ps <- lookupAcc p
  let Body decs stms [res] = body
      acc = Index ps [DimSlice (Var v) (Constant $ IntValue $ intValue it 1) (Constant $ IntValue $ intValue it 1)]
  bindAcc <- runBinderT'_ $ letBind (Pattern [] [pat]) (BasicOp acc)
  body' <- revStms stms
  res' <- adjoint res
  p' <- adjoint p
  stms' <- revStms stms
  let body' = Body decs (bindAcc <> stms') [res']
  return $ oneStm (Let (Pattern [] [PatElem p' (Prim t)]) aux (DoLoop [] valPats (ForLoop v it bound []) body'))

revStm stm = error $ "unsupported stm: " ++ pretty stm

revStms :: Stms SOACS -> ADM (Stms SOACS)
revStms (stms :|> stm) = mappend <$> revStms stms <*> (revStm =<< revFwdStm stm)

-- TODO: fix
revBody :: Body -> ADM Body
revBody (Body desc stms res) = do
  stms' <- revStms stms
  return $ Body desc stms' res

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
      op | op' `elem` ["Add", "FAdd"] ->
        runADBind (bindEnv op)  $ do
          x1 <- x' +^ y'
          bindTans pes' x1

      op | op' `elem` ["Sub", "FSub"] -> 
        runADBind (bindEnv op) $ do
          x1 <- x' -^ y'
          bindTans pes' x1

      op | op' `elem` ["Mul", "FMul"] ->
        runADBind (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 +^ x2
          bindTans pes' x3

      op | op' `elem` ["UDiv", "SDiv", "FDiv"] ->
        runADBind (bindEnv op) $ do
          x1 <- x' *^ y
          x2 <- x *^ y'
          x3 <- x1 -^ x2
          x4 <- y *^ y
          x5 <- x3 //^ x4
          bindTans pes' x5
          
      op | op' `elem` ["Pow", "FPow"] ->
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
    where op' = showConstr $ toConstr op
   
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
  t' <- fwdBodyInterleave' t
  f' <- fwdBodyInterleave' f
  withTan pes $ \pes' ->
    m $
    TanStm stm (oneStm (Let (Pattern [] pes') aux (If cond t' f' attr)))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter' body
    withTans pes $ \pes' ->
      m $
      TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body')))

fwdStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM tangent vals
  withTans valParams $ \valParams' -> do
    (_, body') <- fwdBodyAfter' body
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
      (_, body') <- fwdBodyAfter' body
      withTans pes $ \pes' ->
        m $
        TanStm stm (oneStm (Let (Pattern [] pes') aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop i it bound (loop_vars ++ loop_vars')) body')))

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
  where f tStm = oneStm (primalStm tStm) <> tanStms tStm

fwdStmsAfter :: Stms SOACS -> ADM (Stms SOACS, Stms SOACS) -> ADM (Stms SOACS, Stms SOACS)
fwdStmsAfter = fwdStms f
  where f tStm = (oneStm (primalStm tStm), tanStms tStm)

fwdBodyInterleave :: Stms SOACS -> ADM Body -> ADM Body
fwdBodyInterleave stms m =
  case stms of
    (stm :<| stms') ->
      fwdStm stm $ \tStm -> do
        Body _ stms'' res <- fwdBodyInterleave stms' m
        return $ mkBody (oneStm (primalStm tStm) <> tanStms tStm <> stms'') res
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
        return $ (mkBody (oneStm (primalStm tStm) <> stms1) res1, mkBody ((tanStms tStm) <> stms2) res2)
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
  flip runADM initial_renv $ inScopeOf consts $ inScopeOf fundef $
    withTans (funDefParams fundef) $ \params' -> do
    let params = funDefParams fundef
    (Body attr stms res) <- revBody $ funDefBody fundef
    -- let rts = funDefRetType fundef ++ map paramAttr params
    return $ fundef { funDefParams = funDefParams fundef -- ++ resVNames
                  , funDefBody = Body attr stms res
                  , funDefRetType = concatMap (replicate (length params + 0)) $ funDefRetType fundef -- ridiculous, fix
                  , funDefEntryPoint = (\(a, r) -> (a, concat (replicate (length params + 1) r))) <$> (funDefEntryPoint fundef)
                  }
      
revPass :: Pass SOACS SOACS
revPass =
  Pass { passName = "reverse automatic differentiation"
       , passDescription = "apply reverse automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure revFun
       }
