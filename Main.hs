module Main (main) where

import           Control.Category                          ((>>>))
import           Control.Monad.State
import           Data.List                                 (sortOn, isPrefixOf)
import           Debug.Trace
import           GHC.IO.Encoding                           (setLocaleEncoding)
import           System.Directory
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
import           Futhark.IR.Seq                as RSeq
import           Futhark.IR.SeqMem             (SeqMem)
import           Futhark.IR.SOACS
import           Futhark.Util
import           Futhark.Util.Options
import           Futhark.Util.Pretty                       (pretty)

import Differentiate


sequentialADPipeline :: Pass SOACS SOACS -> Pipeline SOACS RSeq.Seq
sequentialADPipeline p =
  standardPipeline >>>
  onePass p >>>
  onePass firstOrderTransform >>>
  passes [ simplifySeq
         , inPlaceLoweringSeq
         ]

sequentialCpuADPipeline :: Pass SOACS SOACS -> Pipeline SOACS SeqMem
sequentialCpuADPipeline p =
  sequentialADPipeline p >>>
  onePass Seq.explicitAllocations >>>
  passes [ performCSE False
         , simplifySeqMem
         , simplifySeqMem
         ]


type Command = String -> [String] -> IO ()

grad :: Pass SOACS SOACS -> Command
grad p _ [file] = do
              runCompilerOnProgram
               newFutharkConfig
               (standardPipeline >>> onePass p)
               printAction
               file

commands :: [(String, (Command, String))]
commands = sortOn fst
           [ ("fwd", (grad fwdPass, ""))
           , ("rev", (grad revPass, ""))
           , ("fwd-python", (mkPython fwdPass, ""))
           , ("rev-python", (mkPython revPass, ""))
           ]

mkPython :: Pass SOACS SOACS -> String -> [String] -> IO ()
mkPython p = compilerMain () []
       "Compile sequential Python" "Generate sequential Python code from optimised Futhark program."
       (sequentialCpuADPipeline p) $ \() mode outpath prog -> do
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
