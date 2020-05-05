{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Control.Category ((>>>))
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import System.Environment (getArgs)

import Futhark.Binder
import Futhark.Construct
import Futhark.Compiler (runCompilerOnProgram, newFutharkConfig)
import Futhark.Pipeline (onePass)
import Futhark.Passes (standardPipeline)
import Futhark.Actions (printAction)
import Futhark.MonadFreshNames
import Futhark.Pass
import Futhark.Representation.SOACS
import Futhark.Util.Pretty (pretty)

data Env = Env { envGrads :: M.Map VName VName
                 -- ^ If something is not in this map, then it has a
                 -- gradient of zero.
               , envScope :: Scope SOACS
               }

-- A handy monad that keeps track of the most important information we
-- will need: type information, a source of fresh names, a mapping
-- from variables to their derivative, and a convenient way of
-- constructing new statements (the "Binder" monad).
newtype ADM a = ADM (ReaderT Env (State VNameSource) a)
  deriving (Functor, Applicative, Monad,
            MonadReader Env, MonadFreshNames)

instance HasScope SOACS ADM where
  askScope = asks envScope

instance LocalScope SOACS ADM where
  localScope scope = local $ \env -> env { envScope = scope <> envScope env }

runADM :: MonadFreshNames m => ADM a -> Env -> m a
runADM (ADM m) env =
  modifyNameSource $ runState (runReaderT m env)

-- | Create a zero gradient of the desired type.
zeroGrad :: Type -> ADM SubExp
zeroGrad (Prim t) = return $ constant $ blankPrimValue t

subExpGrad :: SubExp -> ADM SubExp
subExpGrad (Constant v) =
  zeroGrad $ Prim $ primValueType v
subExpGrad (Var v) = do
  t <- lookupType v
  maybe_grad <- asks $ M.lookup v . envGrads
  case maybe_grad of
    Nothing -> zeroGrad t
    Just grad -> return $ Var grad

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

onStm :: Stm -> (Stms SOACS -> ADM a) -> ADM a

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (SubExp se))) m = do
  se' <- subExpGrad se
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (SubExp se')))

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Mul it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runBinder_ $ do
      a <- letSubExp "a" $ BasicOp $ BinOp (Mul it) x' y
      b <- letSubExp "b" $ BasicOp $ BinOp (Mul it) x y'
      letBindNames_ [patElemName pe'] $ BasicOp $ BinOp (Add it) a b
    m $ oneStm stm <> stms

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Add it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (BinOp (Add it) x' y')))

onStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm

onStms :: Stms SOACS -> ADM Body -> ADM Body
onStms stms m
  | Just (stm, stms_tail) <- stmsHead stms =
      onStm stm $ \stm_stms -> do
        Body _ stms_tail' res <- onStms stms_tail m
        return $ mkBody (stm_stms<>stms_tail') res
  | otherwise = m

onBody :: Body -> ADM Body
onBody (Body _ stms res) =
  onStms stms $ do
  res' <- mapM subExpGrad res
  return $ mkBody mempty $ res ++ res'

onFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
onFun consts fundef = do
  -- The 'consts' are top-level constants.  They are not important;
  -- don't worry about them, and assume they all have zero gradient.
  let initial_env = Env { envGrads = mempty, envScope = mempty }
  flip runADM initial_env $ inScopeOf consts $
    withParamGrads (funDefParams fundef) $ \gradient_params -> do
    body_with_gradients <- onBody $ funDefBody fundef
    return fundef { funDefParams = funDefParams fundef ++ gradient_params
                  , funDefBody = body_with_gradients
                  , funDefRetType = funDefRetType fundef ++ funDefRetType fundef
                  }

adPass :: Pass SOACS SOACS
adPass =
  Pass { passName = "automatic differenation"
       , passDescription = "apply automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure onFun
       }

main :: IO ()
main = do
  [file] <- getArgs
  runCompilerOnProgram
    newFutharkConfig
    (standardPipeline >>> onePass adPass)
    printAction
    file
