{-|
Module      : Antiprenexor
Description : Main file for WSkS formulae antiprenexing.
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

import System.Environment
import Control.Monad.Writer
import Data.Time

import MonaFormulaOperation
import MonaFormulaAntiprenex

import qualified BaseDecisionProcedure as BP
import qualified Data.Map as Map
import qualified LazyDecisionProcedure as LDP
import qualified StrictDecisionProcedure as SDP
import qualified Logic as Lo
import qualified FormulaOperation as FO
import qualified MonaFormulaOperationSubst as FOS
import qualified Examples as Ex
import qualified MonaWrapper as MoWr
import qualified MonaParser as MoPa
import qualified BasicAutomata as BA
import qualified MonaSocket as MS


-- |Rename bound vars.
renameBoundVars = False

-- |Parameters of the decision procedure.
data ProcedureArgs =
  Prenex
  | None
  deriving (Eq)

-- |Program arguments.
data ProgArgs =
  Antiprenex FilePath
  | Help
  | Error


-- |Parse program arguments.
parseArgs :: [String] -> ProgArgs
parseArgs args
  | (length args) == 1 && (last args) == "--help" = Help
  | (length args) == 1 = Antiprenex (head args)
  | otherwise = Error


-- |Show formula and its simplicication for debug purposes.
formulaOperationsDebug :: Lo.Formula -> IO ()
formulaOperationsDebug f = do
  let sf = FO.simplifyFormula f in do
    putStrLn $ show $ FO.antiprenex sf
    putStrLn $ show $ FO.antiprenex $ FO.balanceFormula sf


-- |Wrap for renaming bound variables in Mona file.
renameBVFileWrap :: MoPa.MonaFile -> MoPa.MonaFile
renameBVFileWrap = if renameBoundVars then FOS.renameBVFile else id


-- |Show help.
showHelp :: IO ()
showHelp = do
  prname <- getProgName
  putStrLn $ "Usage: ./" ++ prname ++ " [file] [args]"
  putStrLn $ "where [args] is one of\n  [--help] show this help"


-- |Main function
main = do
   args <- getArgs
   start <- getCurrentTime
   case (parseArgs args) of
     (Antiprenex file) -> do
       mona <- MoPa.parseFile file
       --putStrLn $ show $ removeRedundantPreds $ renameBVFileWrap $ unwindQuantifFile mona
       putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeRedundantPreds $ replaceCallsFile $ renameBVFileWrap $ unwindQuantifFile mona
       stop <- getCurrentTime
       putStrLn $ "Time: " ++ show (diffUTCTime stop start)
     Help -> showHelp
     Error -> do
       putStrLn $ "Bad input params"
       showHelp
