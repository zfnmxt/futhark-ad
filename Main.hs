{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Main (main) where

import Control.Category ((>>>))
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import Data.Loc
import System.Environment (getArgs)
import Data.Functor.Identity

import Futhark.Binder
import Futhark.Construct
import Futhark.Compiler (runCompilerOnProgram, newFutharkConfig)
import Futhark.Pipeline (onePass)
import Futhark.Passes (standardPipeline)
import Futhark.Actions (printAction)
import Futhark.MonadFreshNames
import Futhark.Pass
import Futhark.Representation.SOACS
import Futhark.Representation.Primitive
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

type ADBind = ReaderT IntType (Binder SOACS)

-- type ADBind = BinderT SOACS (Reader IntType)

runADM :: MonadFreshNames m => ADM a -> Env -> m a
runADM (ADM m) env =
  modifyNameSource $ runState (runReaderT m env)

($^) :: String -> SubExp -> ADBind SubExp
($^) f x = lift $ letSubExp "f x" $ Apply (nameFromString f) [(x, Observe)] [primRetType rt] (Safe, noLoc, mempty)
  where Just (_, rt, _) = M.lookup f primFuns

(+^) :: SubExp -> SubExp -> ADBind SubExp
(+^) x y = do
  it <- ask
  lift $ letSubExp "x+y" $ BasicOp (BinOp (Add it) x y)

(-^) :: SubExp -> SubExp -> ADBind SubExp
(-^) x y = do
  it <- ask
  lift $ letSubExp "x-y" $ BasicOp (BinOp (Sub it) x y)

(*^) :: SubExp -> SubExp -> ADBind SubExp
(*^) x y = do
  it <- ask
  lift $ letSubExp "x*y" $ BasicOp (BinOp (Mul it) x y)

(**^) :: SubExp -> SubExp -> ADBind SubExp
(**^) x y = do
  it <- ask
  lift $ letSubExp "x^y" $ BasicOp (BinOp (Pow it) x y)

mkInt :: IntType -> Int -> SubExp
mkInt it = Constant . IntValue . chooseBits it
  where chooseBits Int8  = Int8Value . toEnum
        chooseBits Int16 = Int16Value . toEnum
        chooseBits Int32 = Int32Value . toEnum
        chooseBits Int64 = Int64Value . toEnum

bindGrads :: PatElem -> SubExp -> ADBind ()
bindGrads pe' se = do
  e <- lift $ eSubExp se
  lift $ letBindNames_ [patElemName pe'] e

runADBind :: IntType -> ADBind a -> ADM (Stms SOACS)
runADBind it m = (runBinder_ . (flip runReaderT) it) m

--(^-) :: SubExp -> SubExp -> ADM Exp
--(^-) x y = do it <- asks intType; return $ BasicOp (BinOp (Sub it) x y)
--
--(^*) :: SubExp -> SubExp -> ADM Exp
--(^*) x y = do it <- asks intType; return $ BasicOp (BinOp (Mul it) x y)

--sAdd :: (MonadBinder m) => IntType -> SubExp -> SubExp -> m SubExp
--sAdd it x y = letSubExp "x+y" $ BasicOp (BinOp (Add it) x y)
--
--sSub :: (MonadBinder m) => IntType -> SubExp -> SubExp -> m SubExp
--sSub it x y = letSubExp "x-y" $ BasicOp (BinOp (Sub it) x y)

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
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Add it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind it $ do
          x1 <- x' +^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Sub it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind it $ do
          x1 <- x' -^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Mul it) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind it $ do
      x1 <- x' *^ y
      x2 <- x *^ y'
      x3 <- x1 +^ x2
      bindGrads pe' x3
    m $ oneStm stm <> stms

-- d/dx (f^g) =  g f^{g - 1} f' + f^g ln(f) g' if f(x) > 0
-- https://en.wikipedia.org/wiki/Differentiation_rules
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Pow it) f g))) m = do
  f' <- subExpGrad f
  g' <- subExpGrad g
  withGrad pe $ \pe' -> do
    stms <- runADBind it $ do
      x1 <- g -^ mkInt it 1 -- x1 = g - 1
      x2 <- f **^ x1        -- x2 = f^x1 = f^{g - 1}
      x3 <- g *^ x2         -- x3 = g f^{g-1} = g x2
      x4 <- x3 *^ f'        -- x4 = g f^{g-1} f' = x3 f'
      x5 <- "log32" $^ f    -- x5 = log (f)  Probably should intelligently select log32 or log64
      x6 <- f **^g          -- x6 = f^g
      x7 <- x6 *^ x5        -- x7 = f^g ln (f) = x6 x5
      x8 <- x7 *^ g'        -- x8 = f^g ln(f) g' = x7 g'
      x9 <- x4 +^ x8        -- x9 = g f^{g - 1} f' + f^g ln(f) g'
      bindGrads pe' x8
    m $ oneStm stm <> stms
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp cOp@CmpOp{})) m = m $ oneStm stm

onStm stm@(Let (Pattern [] [pe]) aux (If cond t f attr)) m = do
  t' <- onBody t
  f' <- onBody f
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (If cond t' f' attr))

onStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

onStms :: Stms SOACS -> ADM Body -> ADM Body
onStms stms m
  | Just (stm, stms_tail) <- stmsHead stms =
      onStm stm $ \stm_stms -> do
        Body _ stms_tail' res <- onStms stms_tail m
        return $ mkBody (stm_stms<>stms_tail') res
  | otherwise = m


--(^+) :: SubExp -> SubExp -> ADM SubExp
--(^+) x y = letSubExp "x8" $ BasicOp $ BinOp (Add it) x y
  

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
