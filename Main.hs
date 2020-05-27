{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
module Main (main) where

import           Control.Category                          ((>>>))
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Functor.Identity
import           Data.List                                 (sortOn)
import           Data.Loc
import qualified Data.Map                                  as M
import           Data.Maybe
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
import           Futhark.IR.Seq                (Seq)
import           Futhark.IR.SeqMem             (SeqMem)
import           Futhark.IR.SOACS
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)


data Env = Env
    { envGrads :: M.Map VName VName
    -- ^ If something is not in this map, then it has a
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

runADM :: MonadFreshNames m => ADM a -> Env -> m a
runADM (ADM m) env =
  modifyNameSource $ runState (runReaderT m env)

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
  maybe_grad <- asks $ M.lookup v . envGrads
  case maybe_grad of
    Nothing   -> zeroGrad t
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

withGrads :: [PatElem] -> ([PatElem] -> ADM a) -> ADM a
withGrads pes m = do
  pes' <- mapM gradPatElem pes
  let f env = env { envGrads = M.fromList (zip (map patElemName pes) (map patElemName pes'))
                               `M.union` envGrads env
                  }
  local f $ m pes'

withGradParams :: [Param attr] -> ([Param attr] -> ADM a) -> ADM a
withGradParams params m = do
  params' <- mapM gradParam params
  let f env = env { envGrads = M.fromList (zip (map paramName params) (map paramName params'))
                               `M.union` envGrads env
                  }
  local f $ m params'

onStm :: Stm -> (Stms SOACS -> ADM a) -> ADM a
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (SubExp se))) m = do
  se' <- subExpGrad se
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (SubExp se')))

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (Opaque se))) m = do
  se' <- subExpGrad se
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (Opaque se')))

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (ArrayLit ses t))) m = do
  ses' <- mapM subExpGrad ses
  traceM $ pretty stm
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (ArrayLit ses' t)))

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (UnOp op x))) m = do
  x' <- subExpGrad x
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (UnOp op x')))

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Add it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf})  $ do
          x1 <- x' +^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FAdd ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft }) $ do
          x1 <- x' +^. y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Sub it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf} ) $ do
          x1 <- x' -^ y'
          bindGrads pe' x1
    m $ oneStm stm <> stms
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FSub ft) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { floatType = ft } ) $ do
          x1 <- x' -^. y'
          bindGrads pe' x1
    m $ oneStm stm <> stms

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Mul it ovf) x y))) m = do
  x' <- subExpGrad x
  y' <- subExpGrad y
  withGrad pe $ \pe' -> do
    stms <- runADBind (defEnv { intType = it, overflow = ovf }) $ do
      x1 <- x' *^ y
      x2 <- x *^ y'
      x3 <- x1 +^ x2
      bindGrads pe' x3
    m $ oneStm stm <> stms
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FMul ft) x y))) m = do
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
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (UDiv it) x y))) m = do
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

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (SDiv it) x y))) m = do
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

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FDiv ft) x y))) m = do
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

onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (ConvOp op x))) m = do
  x' <- subExpGrad x
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (BasicOp (ConvOp op x')))

onStm stm@(Let (Pattern [] [pe]) aux assert@(BasicOp (Assert x err (loc, locs)))) m =
  withGrad pe $ \pe' -> do
    m $
      oneStm stm <>
      oneStm (Let (Pattern [] [pe']) aux assert)

-- d/dx (f^g) =  g f^{g - 1} f' + f^g ln(f) g' if f(x) > 0
-- https://en.wikipedia.org/wiki/Differentiation_rules
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (Pow it) f g))) m = do
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
    
onStm stm@(Let (Pattern [] [pe]) aux (BasicOp (BinOp (FPow ft) f g))) m = do
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

onStm stm@(Let (Pattern [] [pe]) aux cOp@(BasicOp CmpOp{})) m =
  withGrad pe $ \pe' -> do
    m $
      oneStm stm <>
      oneStm (Let (Pattern [] [pe']) aux cOp)

-- TODO: Fix
onStm stm@(Let (Pattern [] [pe]) aux (If cond t f attr)) m = do
  t' <- onBody t
  f' <- onBody f
  withGrad pe $ \pe' ->
    m $
    oneStm stm <>
    oneStm (Let (Pattern [] [pe']) aux (If cond t' f' attr))

onStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' -> do
    body' <- onBody body
    withGrads pes $ \pes' -> do
      m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body'))

onStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop v it bound []) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' -> do
    body' <- onBody body
    withGrads pes $ \pes' -> do
      m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop v it bound []) body'))
      
onStm stm@(Let (Pattern [] pes) aux (DoLoop [] valPats (ForLoop i it bound loop_vars) body)) m = do
  let (valParams, vals) = unzip valPats
  vals' <- mapM subExpGrad vals
  withGradParams valParams $ \valParams' ->
    withGradParams (map fst loop_vars) $ \loopParams' -> do
      let f p n = do n' <- gradVName n; return (p, n')
      loop_vars' <- zipWithM f loopParams' (map snd loop_vars)
      body' <- onBody body
      withGrads pes $ \pes' -> do
        m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (ForLoop i it bound (loop_vars ++ loop_vars')) body'))

onStm stm _ =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

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
                  , funDefEntryPoint = (\(a, r) -> (a ++ a, r ++ r)) <$> (funDefEntryPoint fundef)
                  }

adPass :: Pass SOACS SOACS
adPass =
  Pass { passName = "automatic differenation"
       , passDescription = "apply automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure onFun
       }

pass :: String -> [String] -> IO ()
pass _ [file] = do
              runCompilerOnProgram
               newFutharkConfig
               (standardPipeline >>> onePass adPass)
               printAction
               file

mkPython :: String -> [String] -> IO ()
mkPython = compilerMain () []
       "Compile sequential Python" "Generate sequential Python code from optimised Futhark program."
       sequentialCpuADPipeline $ \() mode outpath prog -> do
          let class_name =
                case mode of ToLibrary    -> Just $ takeBaseName outpath
                             ToExecutable -> Nothing
          pyprog <- SequentialPy.compileProg class_name prog

          case mode of
            ToLibrary ->
              liftIO $ writeFile (outpath `addExtension` "py") pyprog
            ToExecutable -> liftIO $ do
              writeFile outpath pyprog
              perms <- liftIO $ getPermissions outpath
              setPermissions outpath $ setOwnerExecutable True perms

sequentialADPipeline :: Pipeline SOACS Seq
sequentialADPipeline =
  standardPipeline >>>
  onePass adPass >>>
  onePass firstOrderTransform >>>
  passes [ simplifySeq
         , inPlaceLoweringSeq
         ]

sequentialCpuADPipeline :: Pipeline SOACS SeqMem
sequentialCpuADPipeline =
  sequentialADPipeline >>>
  onePass Seq.explicitAllocations >>>
  passes [ performCSE False
         , simplifySeqMem
         , simplifySeqMem
         ]

type Command = String -> [String] -> IO ()
commands :: [(String, (Command, String))]
commands = sortOn fst
           [ ("pass", (pass, ""))
           , ("python", (mkPython, ""))
           ]

msg :: String
msg = unlines $
      ["<command> options...", "Commands:", ""] ++
      [ "   " <> cmd <> replicate (k - length cmd) ' ' <> desc
      | (cmd, (_, desc)) <- commands ]
  where k = maximum (map (length . fst) commands) + 3

main :: IO ()
main = do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  setLocaleEncoding utf8
  args <- getArgs
  prog <- getProgName
  case args of
    cmd:args'
      | Just (m, _) <- lookup cmd commands -> m (unwords [prog, cmd]) args'
    _ -> mainWithOptions () [] msg (const . const Nothing) prog args
