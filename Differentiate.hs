{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
import           Data.List                                 (nub, sortOn, isPrefixOf, intersect, (\\))
import           Data.Loc
import qualified Data.Map                                  as M
import           Data.Maybe
import           Data.Semigroup
import           Data.Sequence                             (Seq(..), fromList)
import qualified Data.Set                                  as S
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
import           Futhark.IR.Prop.Names
import           Futhark.IR.SeqMem                         (SeqMem)
import           Futhark.IR.SOACS
import           Futhark.IR.Traversals
import           Futhark.Transform.Rename
import           Futhark.Transform.Substitute
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)


deriving instance Data Safety
deriving instance Data BinOp
deriving instance Data Overflow
deriving instance Data IntType
deriving instance Data FloatType

--data Adj = Scalar VName
--         | AdjArray Shape 

data Env = Env
    { adjs :: M.Map VName VName
    , tape :: M.Map VName VName
    , vns :: VNameSource
    , envStms :: Stms SOACS
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

pushStm :: Stm -> ADM ()
pushStm = pushStms . oneStm

pushStms :: Stms SOACS -> ADM ()
pushStms stms = modify $ \env -> env { envStms = envStms env <> stms }

popStms :: ADM (Stms SOACS)
popStms = do
  stms <- gets envStms
  modify $ \env -> env { envStms = mempty }
  return stms
  
runADBind :: BindEnv -> ADBind a -> ADM (a, Stms SOACS)
runADBind env m = (runBinder . (flip runReaderT) env) m

runADBind_ :: BindEnv -> ADBind a -> ADM (Stms SOACS)
runADBind_ env m = snd <$> runADBind env m

runADM :: MonadFreshNames m => ADM a -> REnv -> m a
runADM (ADM m) renv =
  modifyNameSource $ \vn -> (\(a, env) -> (a, vns env)) $ runState (runReaderT m renv) (Env mempty mempty vn mempty)

tanVName :: VName -> ADM VName
tanVName v = newVName (baseString v <> "_tan")

adjVName :: VName -> ADM (VName)
adjVName v = newVName (baseString v <> "_adj")

newAdj :: VName -> ADM (VName, M.Map VName VName, Stms SOACS)
newAdj v = do
  _v <- adjVName v
  t <- lookupType v
  let update = M.singleton v _v
  modify $ \env -> env { adjs = update `M.union` adjs env }
  _stms <- runBinderT'_ $ letBindNames [_v] =<< eBlank t
  return (_v, update, _stms)

accVName :: VName -> ADM VName
accVName v = newVName (baseString v <> "_acc")

accVNameLoop :: VName -> ADM VName
accVNameLoop v = newVName (baseString v <> "_acc_loop")

zeroTan :: Type -> ADM SubExp
zeroTan (Prim t) = return $ constant $ blankPrimValue t

mkConst :: (Integral i) => BindEnv -> i -> SubExp
mkConst (IntEnv it _) = Constant . IntValue . intValue it
mkConst (FloatEnv ft) = Constant . FloatValue . floatValue ft

mkConstM :: (Integral i) => i -> ADBind SubExp
mkConstM i = asks ((flip mkConst) i)

insTape :: VName -> VName -> ADM ()
insTape v acc = modify $ \env -> env { tape = M.insert v acc (tape env) }

insAdj :: VName -> VName -> ADM ()
insAdj v _v = modify $ \env -> env { adjs = M.insert v _v (adjs env) }

insAdjMap :: M.Map VName VName -> ADM ()
insAdjMap update = modify $ \env -> env { adjs = update `M.union` adjs env }

lookupTape :: VName -> ADM (Maybe VName)
lookupTape v = gets $ M.lookup v . tape

class Adjoint a where
  lookupAdj :: a -> ADM (VName, M.Map VName VName, Stms SOACS)
  updateAdjoint :: a -> VName -> ADM (VName, M.Map VName VName, Stms SOACS)
  updateAdjointArray :: Maybe (Slice (SubExp)) -> a -> VName -> ADM (VName, M.Map VName VName, Stms SOACS) 
  
instance Adjoint VName where
  lookupAdj v = do
    maybeAdj <- gets $ M.lookup v . adjs
    case maybeAdj of
      Nothing -> newAdj v
      Just _v -> return (_v, mempty, mempty)
      
  updateAdjoint v d = do
    benv <- mkBEnv v
    maybeAdj <- gets $ M.lookup v . adjs
    case maybeAdj of
      Nothing -> setAdjoint v (BasicOp . SubExp . Var $ d)
      Just _v -> do
        (_v', stms) <- runADBind benv $ getVar <$> (Var _v +^ Var d)
        let update = M.singleton v _v'
        insAdjMap update
        return (_v', update, stms)

  updateAdjointArray maybe_slice v d = do
    benv <- mkBEnv v
    maybeAdj <- gets $ M.lookup v . adjs
    t <- lookupType v
    case maybeAdj of
      Nothing -> do
          (_v, us1, s1) <- lookupAdj v
          (_v', us2, s2) <- updateAdjointArray maybe_slice v d
          return (_v', us2 <> us1, s1 <> s2)
      Just _v -> do
        (_v', stms) <- inScopeOf (_v, LParamName t) $ runBinderT' $
          case maybe_slice of
            Nothing -> do
              t'  <- lookupType _v
              letExp "updated_adj" =<< addArrays t' _v d
              
            Just slice -> do
              _vslice <- if primType t
                           then return _v
                           else letExp (baseString _v ++ "_slice") $ BasicOp $ Index _v slice
              t' <- lookupType _vslice
              _vslice' <- addArrays t' _vslice d
              letInPlace "updated_adj" _v slice _vslice'
        let us = M.singleton v _v'
        insAdjMap us
        return (_v', us, stms)
        
   where  bop t = case elemType t of
            ElemPrim (IntType it) -> Add it OverflowWrap
            ElemPrim (FloatType ft) -> FAdd ft

          addArrays t xs ys = 
            case (shapeDims . arrayShape) t of
              [] -> return $ BasicOp $ BinOp (bop t) (Var xs) (Var ys)
              (s:ss) -> do
                lam <- addArrays' $ t `setArrayShape` Shape ss
                return $ Op $ Screma s (mapSOAC lam) [xs, ys]
          addArrays' t =
            case (shapeDims . arrayShape) t of
              [] -> binOpLambda (bop t) $ case elemType t of ElemPrim pt -> pt
              (s:ss) -> do
                xs <- newVName "xs"
                ys <- newVName "ys"
                let t' = t `setArrayShape` Shape ss
                lam <- addArrays' t'
                body <- insertStmsM $ do
                  res <- letSubExp "lam_map" $ Op $ Screma s (mapSOAC lam) [xs, ys]
                  return $ resultBody [res]
                return Lambda { lambdaParams     = [Param xs t', Param ys t']
                              , lambdaReturnType = [t']
                              , lambdaBody       = body
                              }

instance Adjoint SubExp where
  lookupAdj (Constant c) = do
      (_v, stms) <- runBinderT' $ letExp "const_adj" =<< eBlank (Prim $ primValueType c)
      return $ (_v, mempty, stms)
  lookupAdj (Var v) = lookupAdj v

  updateAdjoint se@(Constant c) _ = lookupAdj se
  updateAdjoint (Var v) d = updateAdjoint v d
  
  updateAdjointArray _ se@(Constant c) _ = lookupAdj se
  updateAdjointArray maybe_slice (Var v) d = updateAdjointArray maybe_slice v d

localS :: MonadState s m => (s -> s) -> m a -> m a
localS f m = do
  save <- get
  modify f
  a <- m
  put save
  return a

eIndex :: MonadBinder m => VName -> SubExp -> m (ExpT (Lore m))
eIndex arr i = do
  return . BasicOp . Index arr . pure $ DimFix i

setAdjoint :: VName -> Exp -> ADM (VName, M.Map VName VName, Stms SOACS)
setAdjoint v e = do
  _v <- adjVName v
  stms <- runBinderT'_ $ letBindNames [_v] e
  let update = M.singleton v _v
  insAdjMap update
  return (_v, update, stms)

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


mkBEnv v = do
  t <- lookupType v
  let numEnv = case t of
       (Prim (IntType it)) ->   IntEnv it OverflowWrap
       (Prim (FloatType ft)) -> FloatEnv ft
  return numEnv

revFwdStm :: Stm -> ADM (Stms SOACS)
revFwdStm stm@(Let (Pattern [] pats) aux (DoLoop [] valpats (ForLoop v it bound []) body@(Body decs stms res))) = do
  accs <- mapM (accVName . patElemName) pats
  accsLoop <- mapM (accVName . paramName . fst) valpats

  stms <- runBinderT'_ $ do
    bound' <- letSubExp "bound" $ BasicOp (BinOp (Add it OverflowWrap) bound (Constant $ IntValue $ intValue it 1))
    let accTs     = map (accType bound NoUniqueness . patElemDec) pats
        accTsLoop = map (accType bound Unique . paramDec . fst) valpats
        accPats   = zipWith PatElem accs accTs
    emptyAccs <- forM (zip3 accsLoop accTsLoop accTs) $ \(accLoop, accTLoop, accT) -> do
      blankV  <- letSubExp "empty_acc" =<< eBlank accT
      return (Param accLoop accTLoop, blankV)
    (accsLoop', bodyStms) <- runBinderT' $ do
      accsLoop' <- forM (zip3 accsLoop accTs valpats) $ \(accLoop, accT, (param, _)) ->
          inScopeOf (accLoop, LParamName accT) $ do
            arr_t <- lookupType accLoop
            is' <- mapM (letSubExp "write_i") =<< sequence [toExp v]
            v' <- letSubExp "write_v" =<< (toExp $ paramName param)
            res <- letInPlace "update_acc" accLoop
              (fullSlice arr_t (map DimFix is')) $ BasicOp $ SubExp v'
            return $ Var  res
      addStms stms
      return accsLoop'
    let body' = Body decs bodyStms $ res ++ accsLoop'
    addStm $ Let (Pattern [] (pats ++ accPats)) aux $
               DoLoop [] (valpats ++ emptyAccs) (ForLoop v it bound []) body'
    lift $ zipWithM_ (\pat acc -> insTape (patElemName pat) acc) pats accs
  return stms
  where accType n u (Prim t)                 = Array (ElemPrim t) (Shape [n]) u
        accType n _ (Array t (Shape dims) u) = Array t (Shape (n:dims)) u
        accType _ _ Mem{}                    = error "Mem type encountered."

        emptyAcc (Array t (Shape dims) _) = BasicOp $ Scratch t dims
        emptyAcc _                        = error "Invalid accumulator type."
   
revFwdStm stm = return $ oneStm stm

getVar :: SubExp -> VName
getVar (Var v) = v

revStm :: Stm -> ADM (M.Map VName VName, Stms SOACS)
revStm stm@(Let (Pattern [] pats) aux (DoLoop [] valpats loop@(ForLoop v it bound []) (Body decs_ stms_ res_))) = do
 --fwdStm <- revFwdStm stm
      inScopeOf stm $ localScope (scopeOfFParams $ map fst valpats ++ [Param v (Prim (IntType it))]) $ do
        -- Populate the body with a filler statement if there are none (makes taking adjoints easier).
        body@(Body decs stms res) <-
          if stms_ == mempty
          then do
            (res', stms) <- runBinderT' $
              forM res_ $ \se -> do
                    v <- newVName "filler"
                    letBindNames [v] =<< eSubExp se
                    return $ Var v
            return $ Body decs_ stms res'
          else
            return $ Body decs_ stms_ res_
            
        -- Get the adjoints of the iteration variables.
        let iter_vars = map (paramName . fst) valpats
        (_iter_vars, _iter_map, iter_stms) <- unzip3 <$> mapM lookupAdj iter_vars

        -- "Reset" expressions for the iteration adjoints. Reset expressions just zero-out
        -- the adjoint so that the adjoint on each loop iteration starts from 0. (If you
        -- unroll a loop, each iteration adjoint would be unique and thus start from 0.)
        (_iter_reset, _iter_reset_stms) <- runBinderT' $ forM iter_vars $ \v -> do
          e <- eBlank =<< lookupType v
          letExp "reset" e
          
        -- Construct param-value bindings for the iteration adjoints.
        _iter_params <- inScopeOf (_iter_reset_stms : iter_stms) $ mkBindings _iter_vars _iter_reset

        -- Get adjoints for the free variables in the loop. Iteration
        -- variables are free in the body but bound by the loop, which
        -- is why they're subtracted off.
        let fv = namesToList (freeIn body) \\ iter_vars

        -- Get the adjoints of the result variables
        (_free_vars, _free_map, free_stms) <- unzip3 <$> mapM lookupAdj fv

        -- Generate new names to bind `_free_vars` to `valpats` and
        -- link them to the free variables.
        _free_binds <- forM _free_vars $ newVName . baseString
        zipWithM insAdj fv _free_binds
        
        -- Construct param-value bindings the free variable adjoints.
        _free_params <- inScopeOf free_stms $ mkBindings _free_binds _free_vars

        -- Make adjoints for each result variable of the original body.
        -- The result adjoints of the ith iteration must be set to the
        -- adjoints of the saved loop variables of the i+1th iteration.
        -- Important: this must be done *before* computing the
        -- reverse of the body.
        _original_res <- forM (toVars res) $ \v -> do
              v' <- adjVName v
              insAdj v v'
              return v'

                  -- return (Param _b (toDecl t Unique), Var _v)
        -- Compute the reverse of the body.
        (body_update_map, Body _decs _stms _res) <- inScopeOf (map (\((Param _b t),_) -> (_b, FParamName t)) (_free_params ++ _iter_params)) $
                                                      revBody' body

        (_body_res_vars, _body_res_map, body_res_stms) <- unzip3 <$> mapM lookupAdj (toVars res)

        zipWithM insAdj fv _free_binds

        let body_update_map_free = M.restrictKeys body_update_map $ S.fromList fv
        
        (_iter_vars', _, _) <- unzip3 <$> mapM lookupAdj iter_vars
        let _res' = map Var $ _iter_reset ++ _iter_vars' ++ M.elems body_update_map_free

        -- Remove any free paramters that weren't actually updated in the loop body
        let _free_params' = map fst $ filter (\(p, v) -> v `M.member` body_update_map_free) $ zip _free_params fv

        -- Construct the new return patterns.
        _pats_iter <- inScopeOf (mconcat iter_stms) $ mkPats _iter_vars
        _pats_body_res <- inScopeOf stms $ mkPats' (toVars res) _body_res_vars
        _pats_free_vars <- inScopeOf _stms $ mkPats $ M.elems body_update_map_free
         
        let _pats = _pats_iter ++ _pats_body_res ++ _pats_free_vars

        -- Construct value bindings for the body result adjoints. The initial binding is simply the
        -- adjoint of the nth iteration, which is given by the variables in the original pattern of the let-bind.
        (_loopres, _loopres_map, loopres_stms) <- unzip3 <$> forM pats (\(PatElem p _) -> lookupAdj p)

        let _body_params = zipWith3 (\_b (PatElem _ t) _l  ->  (Param _b (toDecl t Unique), Var _l))
                         _original_res
                         _pats_body_res
                         _loopres

        (bound', boundStms) <- runBinderT' $ letSubExp "bound" $ BasicOp (BinOp (Sub it OverflowWrap) bound (Constant $ IntValue $ intValue it 1))
        
        -- Look-up the stored loop iteration variables. Iteration
        -- variables are the variables bound in `valpats`. Every
        -- iteration of the loop, they are rebound to the result of the
        -- loop body.
        saved_iter_vars_maybe <- sequence <$> mapM (lookupTape . patElemName) pats
        
        (saved_iter_vars, fwdStms) <- case saved_iter_vars_maybe of
          Just saved_iter_vars -> return (saved_iter_vars, mempty)
          Nothing -> do
            fwdStms <- revFwdStm stm
            saved_iter_vars <- sequence <$> mapM (lookupTape . patElemName) pats
            case saved_iter_vars of
              Just saved_iter_vars' -> return (saved_iter_vars', fwdStms)
              Nothing -> error "oops"

        inScopeOf fwdStms $ do
          -- Loop body set-up
          (v', _loopSetup) <- runBinderT' $ do
            -- Go backwards
            v' <- letSubExp "idx" $ BasicOp (BinOp (Sub it OverflowWrap) bound' (Var v))

            -- Bind the accumulators
            forM_ (zip saved_iter_vars valpats) $ \(v, (param, _)) -> 
              letBindNames [paramName param] =<< eIndex v v'

            return v'

          let subst = case v' of Constant{} -> error "oops"; Var v'' -> M.singleton v v''
              _valpats = _iter_params ++ _body_params ++ _free_params'
              _body = Body _decs (_loopSetup <> substituteNames subst _stms) _res'
              _stm = Let (Pattern [] _pats) aux (DoLoop [] _valpats (ForLoop v it bound []) _body)
              
          -- Update the free variables to point to new correct adjoints
          zipWithM_ insAdj fv $ map patElemName _pats_free_vars
          
          -- If any free variables weren't updated, fix their adjoint bindings
          mapM (uncurry insAdj) $ filter (\(v, _) -> v `notElem` M.keys body_update_map_free) $ zip fv _free_vars

          (_, _, final_contrib_stms) <- inScopeOf _stm (unzip3 <$> (mapM (uncurry updateAdjoint) $ map (\(Var v, p) -> (v, p)) $ filter (\(se, p) -> case se of Var v -> True; _ -> False) $ zip (map snd valpats) (map patElemName _pats_body_res)))

          adj_map <- gets adjs

          let changed_fv_map = M.restrictKeys adj_map $ S.fromList (fv ++ namesToList (freeIn (map snd valpats)))

          return (changed_fv_map, fwdStms <> boundStms <> _iter_reset_stms <> mconcat free_stms <> mconcat loopres_stms <> oneStm _stm <> mconcat final_contrib_stms)

        where mkBindings =
                zipWithM $ \_b _v -> do
                  t <- lookupType _v
                  return (Param _b (toDecl t Unique), Var _v)
              toVars :: [SubExp] -> [VName]
              toVars = concatMap (\se -> case se of
                                     Constant{} -> []
                                     Var v      -> [v])
              mkPats = mapM $ \_v -> do
                         t <- lookupType _v
                         _p <- newVName $ baseString _v <> "_res"
                         return $ PatElem _p t
                         
              mkPats' = zipWithM $ \v _v -> do
                         t <- lookupType v
                         _p <- newVName $ baseString _v <> "_res"
                         return $ PatElem _p t
                         
revStm stm@(Let (Pattern [] [pat@(PatElem p t)]) aux cOp@(BasicOp CmpOp{})) = do
  return (mempty, oneStm stm)

revStm stm@(Let (Pattern [] [pat@(PatElem p t)]) aux (BasicOp (BinOp op x y))) = do
  case op of
    op | op' `elem` ["LogAnd", "LogOr"] -> return (mempty, mempty)
    op -> do
      (_p, us1, s1) <- inScopeOf (p, LParamName t) $ lookupAdj $ patElemName pat
      (_x, us2, s2) <- lookupAdj x
      (_y, us3, s3) <- lookupAdj y
      let us = us3 <> us2 <> us1
      let ss = s1 <> s2 <> s3
      case op of
        op | op' `elem` ["Add", "FAdd"] -> do
             (_, us4, s4) <- updateAdjoint x _p
             (_, us5, s5) <- updateAdjoint y _p
             return $ (us5 <> us4 <> us, ss <> s4 <> s5)
        op | op' `elem` ["Sub", "FSub"] -> do
             (_p', s4) <- runADBind (bindEnv op) $ getVar <$> (do zero <- mkConstM 0; zero -^ Var _p)
             (_, us4, s5) <- updateAdjoint x _p'
             (_, us5, s6) <- updateAdjoint y _p'
             return $ (us5 <> us4 <> us, ss <> s4 <> s5 <> s6)

        op | op' `elem` ["Mul", "FMul"] -> do
             (_x', s4) <- runADBind (bindEnv op) $ getVar <$> Var _p *^ y
             (_y', s5) <- runADBind (bindEnv op) $ getVar <$> Var _p *^ x
             (_, us4, s6) <- updateAdjoint x _x'
             (_, us5, s7) <- updateAdjoint y _y'
             return $ (us5 <> us4 <> us, ss <> s4 <> s5 <> s6 <> s7)
  where op' = showConstr $ toConstr op

revStm stm@(Let (Pattern [] pats) aux (If cond t@(Body _ t_stms t_res) f@(Body _ f_stms f_res) attr)) = do
  (_pats, uspats, stm_pats) <- unzip3 <$> mapM (lookupAdj . patElemName) pats
  fwdStms <- revFwdStm stm
  t_fwd <- revFwdStms t_stms
  f_fwd <- revFwdStms f_stms
  zipWithM insAdj (toVars t_res) _pats
  zipWithM insAdj (toVars f_res) _pats
  saved_adjs <- gets adjs
  (t_map, _, _t@(Body t_desc t_stms _t_res)) <- revBody t
  modify $ \env -> env { adjs = saved_adjs}
  (f_map, _, _f@(Body f_desc f_stms _f_res)) <- revBody f
  modify $ \env -> env { adjs = saved_adjs}

  let deltas = sortOn baseTag $ M.keys $ t_map `M.union` f_map

  (_deltas, _, delta_stms) <- unzip3 <$> mapM lookupAdj deltas
  
  _t_res' <- localS (\env -> env {adjs = t_map `M.union` adjs env}) $ do
              (_t_res', _, _) <- unzip3 <$> (mapM lookupAdj $ deltas)
              return _t_res'
              
  _f_res' <- localS (\env -> env {adjs = f_map `M.union` adjs env}) $ do
              (_f_res', _, _) <- unzip3 <$> (mapM lookupAdj $ deltas)
              return _f_res'

  (_pats', res_map) <- unzip <$> forM deltas (\v -> do
    t <- lookupType v
    v' <- adjVName v
    insAdj v v'
    return (PatElem v' t, M.singleton v v'))

  let _t' = Body t_desc (t_fwd <> t_stms) $ map Var _t_res'
      _f' = Body f_desc (f_fwd <> f_stms) $ map Var _f_res'

  ifret <- staticShapes <$> forM deltas lookupType
  let attr' = attr { ifReturns = ifret }

  return (mconcat res_map, fwdStms <> mconcat delta_stms <> oneStm (Let (Pattern [] _pats') aux (If cond _t' _f' attr')))

  where toVars :: [SubExp] -> [VName]
        toVars = concatMap (\se -> case se of
                                    Constant{} -> []
                                    Var v      -> [v])

revStm stm@(Let (Pattern [] [pat@(PatElem p t)]) aux (BasicOp (Index v slice))) = do
  (_p, us1, s1) <- inScopeOf (p, LParamName t) $ lookupAdj $ patElemName pat
  (_, us2, s2) <- updateAdjointArray (Just slice) v _p
  return $ (us2 <> us1, s1 <> s2)
                 
revStm stm@(Let (Pattern [] [pat@(PatElem p t)]) aux (BasicOp (Update v slice se))) = do
  (_p, us1, s1) <- inScopeOf (p, LParamName t) $ lookupAdj $ patElemName pat
  (_pslice, s2) <- inScopeOf (_p, LParamName t) $ runBinderT' $ letExp (baseString _p ++ "_slice") $ BasicOp $ Index _p slice
  (_se, us3, s3) <- updateAdjointArray Nothing se _pslice
  (_v, us4, s4) <- lookupAdj  v
  t' <- case se of
          Constant c -> return $ Prim $ primValueType c
          Var v -> lookupType v
  (_vslice, s5) <- inScopeOf (_v, LParamName t') $ runBinderT' $ letExp (baseString _v ++ "_slice") $ BasicOp $ Index _v slice
  (_se', us6, s6) <- updateAdjoint se _vslice
  return (us6 <> us4<> us3 <> us1, s1 <> s2 <> s3 <> s4 <> s5 <> s6)
  
revStm stm@(Let (Pattern [] [pat@(PatElem p t)]) aux (BasicOp (SubExp se)))
  | Var v <- se = do
    (_p, us1, s1) <- inScopeOf (p, LParamName t) $ lookupAdj $ patElemName pat
    (_, us2, s2)  <- updateAdjoint v _p
    return (us2 <> us1, s1 <> s2)
  | otherwise = return (mempty, mempty)
  
revStm stm@(Let (Pattern [] p) aux (BasicOp (Reshape change v))) = do
    maybeAdj <- gets $ M.lookup v . adjs
    case maybeAdj of
      Nothing -> return (mempty, mempty)
      Just _v -> do
        (_v', stms) <- runBinderT' $ letExp "reshape_adj" (BasicOp (Reshape change _v))
        return (M.singleton v _v', stms)

revStm (Let Pattern{} aux (BasicOp Assert{})) =
  return (mempty, mempty)

revStm stm = error $ "unsupported stm: " ++ pretty stm ++ "\n\n\n" ++ show stm

revFwdStms :: Stms SOACS -> ADM (Stms SOACS)
revFwdStms (stm :<| stms) = do
  fwdStm <- revFwdStm stm
  fwdStms <- revFwdStms stms
  return $ fwdStm <> fwdStms
revFwdStms mempty = return mempty

revStms :: Stms SOACS -> ADM (M.Map VName VName, Stms SOACS, Stms SOACS)
revStms stms = revStms' stms
  where  revStms' (stms  :|> stm) = do
           fwdStm <- revFwdStm stm
           (u, _stm)   <- inScopeOf fwdStm $ revStm stm
           (us, fwdStms, _stms) <- inScopeOf _stm $ revStms' stms
           return (us <> u, fwdStms <> fwdStm, _stm <> _stms)
         revStms' mempty = return (M.empty, mempty, mempty)
         
revStms' :: Stms SOACS -> ADM (M.Map VName VName, Stms SOACS)
revStms' stms = revStms' stms
  where  revStms' (stms  :|> stm) = do
           (u, _stm)   <- revStm stm
           (us, _stms) <- revStms' stms
           return (us <> u, _stm <> _stms)
         revStms' mempty = return (M.empty, mempty)

revBody :: Body -> ADM (M.Map VName VName, Body, Body)
revBody b@(Body desc stms res) = do
  (us, fwdStms, _stms) <- revStms stms
  let fv  = namesToList $ freeIn b
      us' = M.filterWithKey (\k _ -> k `elem` fv) us
  let body' = Body desc _stms $ map Var $ M.elems us'
  return (us', Body desc fwdStms res, body')
  
revBody' :: Body -> ADM (M.Map VName VName, Body)
revBody' b@(Body desc stms res) = do
  (us, _stms) <- inScopeOf stms $ revStms' stms
  let fv  = namesToList $ freeIn b
      us' = M.filterWithKey (\k _ -> k `elem` fv) us
  let body' = Body desc _stms $ map Var $ M.elems us'
  return (us, body')

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
             IntEnv it _ -> SDiv it Unsafe
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
bindEnv (UDiv it _)  = IntEnv it OverflowWrap
bindEnv (SDiv it _)  = IntEnv it OverflowWrap
bindEnv (FDiv ft)    = FloatEnv ft
bindEnv (Pow it)     = IntEnv it OverflowWrap
bindEnv (FPow ft)    = FloatEnv ft
--
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
    error $ pretty $ fundef { funDefParams = funDefParams fundef ++ params'
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
revFun consts fundef@(FunDef entry _attrs name ret params body@(Body decs stms res)) = do
  let initial_renv = REnv { tans = mempty, envScope = mempty }
  flip runADM initial_renv $ inScopeOf consts $ inScopeOf fundef $ inScopeOf stms $ do
    traceM $ pretty fundef ++ "\n" ++ show fundef ++ "\n"
    let rvars  = concatMap (\se -> case se of Constant{} -> []; Var v -> [v]) res
    
    _params <- zipWithM (\v t -> do
                           _v <- adjVName v
                           insAdj v _v
                           _t <- lookupType v
                           --return $ Param _v (removeExtShapes t)) rvars ret
                           return $ Param _v (toDecl _t Nonunique)) rvars ret
               
    (body_us, fwdBody@(Body fwdDecs fwdStms fwdRes), _body) <- revBody body
    
    (Body _decs _stms _res) <- renameBody _body
    let _rvars = concatMap (\se -> case se of Constant{} -> []; Var v -> [v]) _res

    _ret <- inScopeOf (stms <> _stms) $ concat <$> forM _res (\se ->
      case se of
        Constant{} -> return []
        Var v -> do
          t <- lookupType v
          return $ pure $ staticShapes1 $ toDecl t Unique)
            
    let _entry = (flip fmap) entry $ \(as, rs) ->
         let _as = as ++ map (const TypeDirect) _rvars
             _rs = as
         in (_as, _rs)

    let rev = fundef { funDefEntryPoint = (\(as1, rs1) (as2, rs2) -> (as1 ++ as2, rs1 ++ rs2)) <$> entry <*> _entry
                    , funDefRetType = _ret
                    , funDefParams = params ++ _params
                    , funDefBody = Body _decs (fwdStms <> _stms) _res
                    }
    traceM $ "\nprimal:\n" ++ pretty fundef
    traceM $ "\nreverse:\n" ++ pretty rev
    return rev
    where removeExtShapes :: DeclExtType -> DeclType
          removeExtShapes (Prim t) = Prim t
          removeExtShapes (Array t (Shape ext_se) u) =  Array t (Shape (map (\(Free se) -> se) ext_se)) u
          removeExtShapes (Mem space) = Mem space
      
revPass :: Pass SOACS SOACS
revPass =
  Pass { passName = "reverse automatic differentiation"
       , passDescription = "apply reverse automatic differentiation to all functions"
       , passFunction = intraproceduralTransformationWithConsts pure revFun
       }
