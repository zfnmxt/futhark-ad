{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Differentiate (revPass, fwdPass) where

import           Control.Category                          ((>>>))
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Functor.Identity
import           Data.List                                 (sortOn, isPrefixOf, isInfixOf)
import           Data.Loc
import qualified Data.Map                                  as M
import           Data.Maybe
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
import           Futhark.IR.SeqMem             (SeqMem)
import           Futhark.IR.SOACS
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)


data REnv = REnv
    { envGrads :: M.Map VName VName
    -- ^ If something is not in this map, then it has a
    , envScope :: Scope SOACS
    }
    
data Env = Env
    { envAdjoints :: M.Map VName Adjoint
    , vns :: VNameSource
    }
    
type Adjoint = (ADBind SubExp, VName)

-- A handy monad that keeps track of the most important information we
-- will need: type information, a source of fresh names, a mapping
-- from variables to their derivative, and a convenient way of
-- constructing new statements (the "Binder" monad).
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

data BEnv = BEnv
    { intType   :: IntType
    , floatType :: FloatType
    , overflow  :: Overflow
    }

defEnv :: BEnv
defEnv = BEnv { intType = Int32
              , floatType = Float32
              , overflow = OverflowWrap
              }

type ADBind = ReaderT BEnv (Binder SOACS)

runADM :: MonadFreshNames m => ADM a -> REnv -> m a
runADM (ADM m) env =
  modifyNameSource $ \vn -> (\(a, env) -> (a, vns env)) $ runState (runReaderT m env) (Env mempty vn)
  
-- modifyNameSource :: MonadFreshNames m => (VNameSource -> (a, VNameSource)) -> m a

($^) :: String -> SubExp -> ADBind SubExp
($^) f x = lift $ letSubExp "f x" $ Apply (nameFromString f) [(x, Observe)] [primRetType rt] (Safe, noLoc, mempty)
  where Just (_, rt, _) = M.lookup f primFuns

(+^) :: SubExp -> SubExp -> ADBind SubExp
(+^) x y = do
  it  <- asks intType
  ovf <- asks overflow
  lift $ letSubExp "x+^y" $ BasicOp (BinOp (Add it ovf) x y)
  
(+^.) :: SubExp -> SubExp -> ADBind SubExp
(+^.) x y = do
  ft <- asks floatType
  lift $ letSubExp "x+^.y" $ BasicOp (BinOp (FAdd ft) x y)

(-^) :: SubExp -> SubExp -> ADBind SubExp
(-^) x y = do
  it  <- asks intType
  ovf <- asks overflow
  lift $ letSubExp "x-^y" $ BasicOp (BinOp (Sub it ovf) x y)

(-^.) :: SubExp -> SubExp -> ADBind SubExp
(-^.) x y = do
  ft <- asks floatType
  lift $ letSubExp "x-^.y" $ BasicOp (BinOp (FSub ft) x y)

(*^) :: SubExp -> SubExp -> ADBind SubExp
(*^) x y = do
  it  <- asks intType
  ovf <- asks overflow
  lift $ letSubExp "x*^y" $ BasicOp (BinOp (Mul it ovf) x y)
  
(*^.) :: SubExp -> SubExp -> ADBind SubExp
(*^.) x y = do
  ft <- asks floatType
  lift $ letSubExp "x*^.y" $ BasicOp (BinOp (FMul ft) x y)

(//^) :: SubExp -> SubExp -> ADBind SubExp
(//^) x y = do
  it <- asks intType
  lift $ letSubExp "x//^y" $ BasicOp (BinOp (SDiv it) x y)

(/^.) :: SubExp -> SubExp -> ADBind SubExp
(/^.) x y = do
  ft <- asks floatType
  lift $ letSubExp "x/^.y" $ BasicOp (BinOp (FDiv ft) x y)

(**^) :: SubExp -> SubExp -> ADBind SubExp
(**^) x y = do
  it <- asks intType
  lift $ letSubExp "x**^y" $ BasicOp (BinOp (Pow it) x y)
  
(**^.) :: SubExp -> SubExp -> ADBind SubExp
(**^.) x y = do
  ft <- asks floatType
  lift $ letSubExp "x**^.y" $ BasicOp (BinOp (FPow ft) x y)

mkInt :: (Integral i) => IntType -> i -> SubExp
mkInt it = Constant . IntValue . intValue it
        
mkFloat :: (Real num) => FloatType -> num -> SubExp
mkFloat ft = Constant . FloatValue . floatValue ft

mkPrimValue :: (Integral num) => num -> PrimType -> PrimValue
mkPrimtValue num (IntType it) = IntValue $ intValue it num
mkPrimValue num (FloatType ft) = FloatValue $ floatValue ft num
mkPrimValue _ _ = error "oops"

bindGrads :: PatElem -> SubExp -> ADBind ()
bindGrads pe' se = do
  e <- lift $ eSubExp se
  lift $ letBindNames [patElemName pe'] e

runADBind :: BEnv -> ADBind a -> ADM (Stms SOACS)
runADBind env m = (runBinder_ . (flip runReaderT) env) m

-- | Create a zero gradient of the desired type.
zeroGrad :: Type -> ADM SubExp
zeroGrad (Prim t) = return $ constant $ blankPrimValue t

gradVName :: VName -> ADM VName
gradVName n = do
 maybe_grad <- asks $ M.lookup n . envGrads
 case maybe_grad of
   Nothing -> error "oops"
   Just grad -> return grad

subExpGrad :: SubExp -> ADM SubExp
subExpGrad (Constant v) =
  zeroGrad $ Prim $ primValueType v
subExpGrad (Var v) = do
  t <- lookupType v
  maybe_adjoint <- gets $ M.lookup v . envAdjoints
  maybe_grad <- asks $ M.lookup v . envGrads
  case (maybe_adjoint, maybe_grad) of
    (Just (_, grad), _) -> return $ Var grad
    (_, Just grad) -> return $ Var grad
    _   -> zeroGrad t

gradParam :: Param attr -> ADM (Param attr)
gradParam (Param p t) = do
  Param <$> newVName (baseString p <> "_grad") <*> pure t

gradPatElem :: PatElem -> ADM PatElem
gradPatElem (PatElem p t) =
  PatElem <$> newVName (baseString p <> "_grad") <*> pure t

-- Produce a new parameter for each input parameter, which will
-- represent the gradient of that parameter.
gradientsForParams :: Typed attr => [Param attr] -> ADM [Param attr]
gradientsForParams = mapM gradParam

withParamGrads :: Typed attr =>
                  [Param attr] -> ([Param attr] -> ADM a) -> ADM a
withParamGrads ps f = do
  ps' <- gradientsForParams ps
  let mapping = M.fromList $ zip (map paramName ps) (map paramName ps')
  local (\env -> env { envGrads = mapping <> envGrads env }) $ f ps'

withGrad :: PatElem -> (PatElem -> ADM a) -> ADM a
withGrad pe m = do
  pe' <- gradPatElem pe
  let f env = env { envGrads = M.insert (patElemName pe) (patElemName pe') $
                               envGrads env
                  }
  local f $ m pe'

withGrads :: [PatElem] -> ([PatElem] -> ADM a) -> ADM a
withGrads pes m = do
  pes' <- mapM gradPatElem pes
  let f env = env { envGrads = M.fromList (zip (map patElemName pes) (map patElemName pes'))
                               `M.union` envGrads env
                  }
  local f $ m pes'

withGradsRev :: [PatElem] -> ([PatElem] -> ADM a) -> ADM a
withGradsRev pes m = do
  pes' <- mapM gradPatElem pes
  let f env = env { envGrads = M.fromList (zip (map patElemName pes) (map patElemName pes'))
                               `M.union` envGrads env
                  }
  local f $ m pes'

withGradParams :: [Param attr] -> ([Param attr] -> ADM a) -> ADM a
withGradParams params m = do
  params' <- mapM gradParam params
  let f rEnv = rEnv { envGrads = M.fromList (zip (map paramName params) (map paramName params'))
                               `M.union` envGrads rEnv
                     }
  modify $ \env -> env { envAdjoints =  M.fromList (zip (map paramName params) (map (\p' -> (return (Var (paramName p')), paramName p')) params'))
                                       `M.union` envAdjoints env
                       }
  local f $ m params'
  
lookupAdjoint :: VName -> ADM (Adjoint)
lookupAdjoint v = do
  maybeAdjoints  <- gets $ (M.!? v) . envAdjoints 
  case maybeAdjoints of
    Just adjoint -> return adjoint
    Nothing -> do
      vbar <- adjointVName v
      t <- lookupType v
      let adjoint = if ("res" `isPrefixOf` baseString v)
                      then (return (mkFloat Float32 1), vbar) -- awful hack, fix
                      else case t of
                        (Prim t') -> (return (constant (blankPrimValue t')), vbar)
                        _ -> error ""
      modify $ \env -> env { envAdjoints = M.insert v adjoint (envAdjoints env) }
      return adjoint
    
insertAdjoint :: VName -> VName -> SubExp -> ADM ()
insertAdjoint p v se = do
  (_, pbar) <- lookupAdjoint p
  (mVse, vbar) <- lookupAdjoint v
  let mVse' = do
       vse <- mVse
       vse' <- (Var pbar) *^. se
       vse' +^. vse
     in modify $ \env -> env { envAdjoints = M.insert v (mVse', vbar) (envAdjoints env) }
                         
subExpAdjoint :: VName -> SubExp -> SubExp -> ADM ()
subExpAdjoint _ (Constant v) _ = return ()
subExpAdjoint p (Var v) se = insertAdjoint p v se

dStm :: Stm -> (Stms SOACS -> ADM a) -> ADM a
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (SubExp se))) m = do
  se' <- subExpGrad se
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (SubExp se')))

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (Opaque se))) m = do
  se' <- subExpGrad se
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (Opaque se')))

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (ArrayLit ses t))) m = do
  ses' <- mapM subExpGrad ses
  traceM $ pretty stm
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (ArrayLit ses' t)))

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (UnOp op x))) m = do
  x' <- subExpGrad x
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (UnOp op x')))

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Add it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf})  $ do
          x1 <- x' +^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms
    
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FAdd ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft }) $ do
          x1 <- x' +^. y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Sub it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf} ) $ do
          x1 <- x' -^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms
    
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FSub ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft } ) $ do
          x1 <- x' -^. y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Mul it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf }) $ do
      x1 <- x' *^ y
      x2 <- x *^ y'
      x3 <- x1 +^ x2
      bindGrads pe' x3
    m $ oneStm stm <> stms
    
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FMul ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft }) $ do
      x1 <- x' *^. y
      x2 <- x *^. y'
      x3 <- x1 +^. x2
      bindGrads pe' x3
    m $ oneStm stm <> stms

-- Derivatives are signed (maybe they shouldn't be?)
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (UDiv it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it }) $ do
      x1 <- x' *^ y
      x2 <- x *^ y'
      x3 <- x1 -^ x2
      x4 <- y *^ y
      x5 <- x3 //^ x4
      bindGrads pe' x5
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (SDiv it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it }) $ do
      x1 <- x' *^ y
      x2 <- x *^ y'
      x3 <- x1 -^ x2
      x4 <- y *^ y
      x5 <- x3 //^ x4
      bindGrads pe' x5
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FDiv ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft }) $ do
      x1 <- x' *^. y
      x2 <- x *^. y'
      x3 <- x1 -^. x2
      x4 <- y *^. y
      x5 <- x3 /^. x4
      bindGrads pe' x5
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (ConvOp op x))) m = do
  x' <- subExpGrad x
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (ConvOp op x')))

dStm stm@(Let (Pattern [] [pe]) aux assert@(BasicOp (Assert x err (loc, locs)))) m =
  withGrad pe $ \pe' -> do
    m $
      oneStm stm <>
      oneStm (Let (Pattern [] [pe']) aux assert)

-- d/dx (f^g) =  g f^{g - 1} f' + f^g ln(f) g' if f(x) > 0
-- https://en.wikipedia.org/wiki/Differentiation_rules
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Pow it) f g))) m = do
  f' <- subExpGrad f
  g' <- subExpGrad g
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it }) $ do
      x1 <- g -^ mkInt it 1 -- x1 = g - 1
      x2 <- f **^ x1        -- x2 = f^x1 = f^{g - 1}
      x3 <- g *^ x2         -- x3 = g f^{g-1} = g x2
      x4 <- x3 *^ f'        -- x4 = g f^{g-1} f' = x3 f'
      x5 <- "log32" $^ f    -- x5 = log (f)  Probably should intelligently select log32 or log64
      x6 <- f **^g          -- x6 = f^g
      x7 <- x6 *^ x5        -- x7 = f^g ln (f) = x6 x5
      x8 <- x7 *^ g'        -- x8 = f^g ln(f) g' = x7 g'
      x9 <- x4 +^ x8        -- x9 = g f^{g - 1} f' + f^g ln(f) g'
      bindGrads pe' x9
    m $ oneStm stm <> stms
    
dStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FPow ft) f g))) m = do
  f' <- subExpGrad f
  g' <- subExpGrad g
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft }) $ do
      x1 <- g -^. mkFloat ft 1 -- x1 = g - 1
      x2 <- f **^. x1        -- x2 = f^x1 = f^{g - 1}
      x3 <- g *^. x2         -- x3 = g f^{g-1} = g x2
      x4 <- x3 *^. f'        -- x4 = g f^{g-1} f' = x3 f'
      x5 <- "log32" $^ f    -- x5 = log (f)  Probably should intelligently select log32 or log64
      x6 <- f **^. g          -- x6 = f^g
      x7 <- x6 *^. x5        -- x7 = f^g ln (f) = x6 x5
      x8 <- x7 *^. g'        -- x8 = f^g ln(f) g' = x7 g'
      x9 <- x4 +^. x8        -- x9 = g f^{g - 1} f' + f^g ln(f) g'
      bindGrads pe' x9
    m $ oneStm stm <> stms

dStm stm@(Let (Pattern [] [pe]) aux cOp@(BasicOp CmpOp{})) m =
  withGrad pe $ \pe' -> do
    m $
      oneStm stm <>
      oneStm (Let (Pattern [] [pe']) aux cOp)

dStm stm@(Let (Pattern [] [pe]) aux (If cond t f attr)) m = do
  t' <- dBody t
  f' <- dBody f
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (If cond t' f' attr))

dStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' -> do
    body' <- dBody body
    withGrads pes $ \pes' -> do
      m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body'))

dStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' -> do
    body' <- dBody body
    withGrads pes $ \pes' -> do
      m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop v it bound []) body'))
      
dStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop i it bound loop_vars) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' ->
    withGradParams (map fst loop_vars) $ \loopParams' -> do
      let f p n = do n' <- gradVName n; return (p, n')
      loop_vars' <- zipWithM f loopParams' (map snd loop_vars)
      body' <- dBody body
      withGrads pes $ \pes' -> do
        m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop i it bound (loop_vars ++ loop_vars')) body'))

dStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

adjointStm :: Stm -> ADM ()
adjointStm (Let (Pattern [] [pe@(PatElem p t)]) aux (BasicOp (BinOp (FAdd ft) x y))) = do
  subExpAdjoint p x (mkFloat ft 1)
  subExpAdjoint p y (mkFloat ft 1)
  
adjointStm (Let (Pattern [] [pe@(PatElem p t)]) aux (BasicOp (BinOp (Add _ _) x y))) = do
  subExpAdjoint p x (mkFloat Float32 1)
  subExpAdjoint p y (mkFloat Float32 1)
  
adjointStm (Let (Pattern [] [pe@(PatElem p t)]) aux (BasicOp (BinOp (FMul ft) x y))) = do
  subExpAdjoint p x y
  subExpAdjoint p y x
  
adjointStm (Let (Pattern [] [pe@(PatElem p t)]) aux (BasicOp (BinOp (Mul _ _) x y))) = do
  subExpAdjoint p x y
  subExpAdjoint p y x

adjointStm stm@(Let (Pattern [] [pe@(PatElem p t)]) aux cOp@(BasicOp CmpOp{})) =
  void $ inScopeOf stm $ lookupAdjoint p 

adjointStm stm@(Let (Pattern [] pes) aux (DoLoop{})) = return ()

adjointStm stm =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

fwdAdjoint :: Stm -> ADM ()
fwdAdjoint stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) =
  void $ dStm stm $ \stm' -> do
  valPats' <- mapM (gradVName . paramName . fst) valPats
  forM valPats' $ \v ->
    runBinder_ $ do
      letBindNames [v] (BasicOp $ SubExp $ constant $ mkPrimValue 1 (IntType Int32)) --todo: fix
      letBindNames (filter (/= v) valPats') (BasicOp $ SubExp $ constant $ blankPrimValue (IntType Int32))
      addStms stm'

dStms :: Stms SOACS -> ADM Body -> ADM Body
dStms stms m
  | Just (stm, stms_tail) <- stmsHead stms =
      dStm stm $ \stm_stms -> do
        Body _ stms_tail' res <- dStms stms_tail m
        return $ mkBody (stm_stms<>stms_tail') res
  | otherwise = m

adjointStms :: Stms SOACS -> ADM ()
adjointStms stms
  | Just (stm, stms_tail) <- stmsHead stms = do
      stm' <- adjointStm stm
      stms_tail' <- adjointStms stms_tail
      return ()
  | otherwise = return mempty
  
adjointVName :: VName -> ADM VName
adjointVName v = newVName (baseString v <> "_adjoint")
 
adjointToStms :: VName -> ADM (Stms SOACS)
adjointToStms v = do
  (mSe, vbar) <- lookupAdjoint v
  let mSe' = do
       se <- mSe 
       e <- lift $ eSubExp se
       lift $ letBindNames [vbar] e
  runADBind (BEnv Int32 Float32 OverflowWrap) mSe' -- TODO: fix
  
firstPass :: Body -> ADM ()
firstPass (Body _ stms res) = do
  adjointStms stms

secondPass :: Stms SOACS -> ADM (Stms SOACS)
secondPass Empty = return mempty
--secondPass (stms' :|> stm) =
secondPass (stm :<| stms') = do
  aStms <- case stm of
          (Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) ->
            dStm stm $ \stm' -> do
             let [vn] = [ vn | (_, Var vn) <- tail valPats] --TODO: fix
             --t <- lookupType vn
             --case t of
              -- (Prim t') -> do
             vn' <- gradVName vn
             s <- mkLetNames [vn'] (BasicOp $ SubExp $ constant $ IntValue $ Int32Value 1) -- TODO: fix
             f $ oneStm s <> stm'
               --_ -> error ""
            
          _ -> do
            let (Pattern [] pats) = stmPattern stm
            (oneStm stm <>) <$> foldM (\s p -> (s <>) <$> adjointToStms (patElemName p)) mempty pats
  let (Pattern [] pats) = stmPattern stm
  withGrads pats $ \_ -> f aStms
  where f aStms = do
         aStms' <- secondPass stms'
         return $ aStms <> aStms'
         
dBody :: Body -> ADM Body
dBody (Body _ stms res) =
  dStms stms $ do
  res' <- mapM subExpGrad res
  return $ mkBody mempty $ res ++ res'
  
revBody ::  Body -> ADM Body 
revBody body@(Body _ stms res) = do
  firstPass body
  adjointStms <- secondPass stms
  return $ mkBody adjointStms res

dFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
dFun consts fundef = do
  -- The 'consts' are top-level constants.  They are not important;
  -- don't worry about them, and assume they all have zero gradient.
  let initial_renv = REnv { envGrads = mempty, envScope = mempty }
  flip runADM initial_renv $ inScopeOf consts $
    withParamGrads (funDefParams fundef) $ \gradient_params -> do
    body_with_gradients <- dBody $ funDefBody fundef
    return fundef { funDefParams = funDefParams fundef ++ gradient_params
                  , funDefBody = body_with_gradients
                  , funDefRetType = funDefRetType fundef ++ funDefRetType fundef
                  , funDefEntryPoint = (\(a, r) -> (a ++ a, r ++ r)) <$> (funDefEntryPoint fundef)
                  }

revFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
revFun consts fundef = do
  -- The 'consts' are top-level constants.  They are not important;
  -- don't worry about them, and assume they all have zero gradient.

  let initial_renv = REnv { envGrads = mempty, envScope = mempty }
  flip runADM initial_renv $ inScopeOf consts $ inScopeOf fundef $
    withParamGrads (funDefParams fundef) $ \gradient_params -> do
    let params = funDefParams fundef
    (Body attr stms res) <- revBody $ funDefBody fundef
    adjointParams <- foldM (\s p -> (s <>) <$> (adjointToStms (paramName p))) mempty params
    m <- gets envAdjoints
    let res' = res ++ map (Var . snd . (m M.!) . paramName) params
    -- let rts = funDefRetType fundef ++ map paramAttr params
    return $ fundef { funDefParams = funDefParams fundef -- ++ resVNames
                  , funDefBody = Body attr (stms <> adjointParams) res'
                  , funDefRetType = concatMap (replicate (length params + 1)) $ funDefRetType fundef -- ridiculous, fix
                  , funDefEntryPoint = (\(a, r) -> (a, concat (replicate (length params + 1) r))) <$> (funDefEntryPoint fundef)
                  }
      
fwdPass :: Pass SOACS SOACS
fwdPass =
  Pass { passName = "automatic differenation"
       , passDescription = "apply automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure dFun
       }
  
revPass :: Pass SOACS SOACS
revPass =
  Pass { passName = "reverse automatic differentiation"
       , passDescription = "apply reverse automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure revFun
       }
