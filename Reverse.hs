{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Reverse where

import           Control.Category                          ((>>>))
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Functor.Identity
import           Data.List                                 (sortOn, isPrefixOf)
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
import           Futhark.Representation.Primitive
import qualified Futhark.Representation.Seq                as RepSeq
import           Futhark.Representation.SeqMem             (SeqMem)
import           Futhark.Representation.SOACS
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)


type ADBind = ReaderT BEnv (Binder SOACS)


data BEnv = BEnv
    { intType   :: IntType
    , floatType :: FloatType
    , overflow  :: Overflow
    }

type Adjoint = (ADBind SubExp, VName)

data Env = Env
    { envAdjoints :: M.Map VName Adjoint
    , vns :: VNameSource
    }

-- A handy monad that keeps track of the most important information we
-- will need: type information, a source of fresh names, a mapping
-- from variables to their derivative, and a convenient way of
-- constructing new statements (the "Binder" monad).
newtype ADM a = ADM (ReaderT (Scope SOACS) (State Env) a)
  deriving (Functor, Applicative, Monad,
            MonadReader (Scope SOACS), MonadState Env, MonadFreshNames)

instance MonadFreshNames (State Env) where
  getNameSource = gets vns
  putNameSource vns' = modify (\env -> env { vns = vns' })

instance HasScope SOACS ADM where
  askScope = ask

instance LocalScope SOACS ADM where
  localScope scope = local (scope <>)

runADM :: MonadFreshNames m => ADM a -> Scope SOACS -> m a
runADM (ADM m) scope =
  modifyNameSource $ \vn -> (\(a, env) -> (a, vns env)) $ runState (runReaderT m scope) (Env mempty vn)

runADBind :: BEnv -> ADBind a -> ADM (Stms SOACS)
runADBind env m = (runBinder_ . (flip runReaderT) env) m
  
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

mkFloat :: (Real num) => FloatType -> num -> SubExp
mkFloat ft = Constant . FloatValue . floatValue ft

lookupAdjoint :: VName -> ADM (Adjoint)
lookupAdjoint v = do
  maybeAdjoints  <- gets $ (M.!? v) . envAdjoints 
  case maybeAdjoints of
    Just adjoint -> return adjoint
    Nothing -> do
      vbar <- adjointVName v
      let adjoint = if ("res" `isPrefixOf` baseString v)
                      then (return (mkFloat Float32 1), vbar) -- awful hack, fix
                      else (return (mkFloat Float32 0), vbar)
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

adjointStm (Let (Pattern [] [pe]) aux cOp@(BasicOp CmpOp{})) = return ()

adjointStm (Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) = do
  firstPass body
  --let (valParams, vals) = unzip valPats
  --vals' <- mapM subExpGrad vals
  --withGradParams valParams $ \valParams' -> do
  --  body' <- onBody body
  --  withGrads pes $ \pes' -> do
  --    m $ oneStm (Let (Pattern [] (pes ++ pes')) aux (DoLoop [] (valPats ++ (zip valParams' vals')) (WhileLoop v) body'))

adjointStm stm =
  error $ "unhandled AD for Stm: " ++ pretty stm ++ "\n" ++ show stm

adjointStms :: Stms SOACS -> ADM ()
adjointStms stms
  | Just (stm, stms_tail) <- stmsHead stms = do
      stm' <- adjointStm stm
      stms_tail' <- adjointStms stms_tail
      return ()
  | otherwise = return mempty

firstPass :: Body -> ADM ()
firstPass (Body _ stms res) = do
  adjointStms stms

secondPass :: Stms SOACS -> ADM (Stms SOACS)
secondPass Empty = return mempty
secondPass (stms' :|> stm) =
  --case stm of
  --  (Let (Pattern [] pes) aux (DoLoop [] valPats (WhileLoop v) body)) ->
  --    
  --  _ -> do
           do
      let (Pattern [] pats) = stmPattern stm
      aStms  <- foldM (\s p -> (s <>) <$> adjointToStms (patElemName p)) mempty pats
      aStms' <- secondPass stms'
      return $ aStms <> aStms'

adjointVName :: VName -> ADM VName
adjointVName v = newVName (baseString v <> "_adjoint")
 
adjointToStms :: VName -> ADM (Stms SOACS)
adjointToStms v = do
  (mSe, vbar) <- lookupAdjoint v
  let mSe' = do
       se <- mSe 
       e <- lift $ eSubExp se
       lift $ letBindNames_ [vbar] e
  runADBind (BEnv Int32 Float32 OverflowWrap) mSe' -- TODO: fix

onBody ::  Body -> ADM Body 
onBody body@(Body _ stms res) = do
  firstPass body
  adjointStms <- secondPass stms
  return $ mkBody (stms <> adjointStms) res


  
onFun :: Stms SOACS -> FunDef SOACS -> PassM (FunDef SOACS)
onFun consts fundef = do
  -- The 'consts' are top-level constants.  They are not important;
  -- don't worry about them, and assume they all have zero gradient.
  let initial_env = Env { envAdjoints = mempty, vns = mempty }
  flip runADM mempty $ inScopeOf consts $ do
    let params = funDefParams fundef
    (Body attr stms res) <- onBody $ funDefBody fundef
    adjointParams <- foldM (\s p -> (s <>) <$> (adjointToStms (paramName p))) mempty params
    m <- gets envAdjoints
    let res' = res ++ map (Var . snd . (m M.!) . paramName) params
    -- let rts = funDefRetType fundef ++ map paramAttr params
    return fundef { funDefParams = funDefParams fundef -- ++ resVNames
                  , funDefBody = Body attr (stms <> adjointParams) res'
                  , funDefRetType = concatMap (replicate (length params + 1)) $ funDefRetType fundef -- ridiculous, fix
                  , funDefEntryPoint = (\(a, r) -> (a, concat (replicate (length params + 1) r))) <$> (funDefEntryPoint fundef)
                  }
      
adPass :: Pass SOACS SOACS
adPass =
  Pass { passName = "reverse automatic differentiation"
       , passDescription = "apply reverse automatic differentiation to all functions"
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

sequentialADPipeline :: Pipeline SOACS RepSeq.Seq
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
