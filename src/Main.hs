{-|
Module      : Main
Description : Main file for WSkS decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

import System.Environment
import Control.Monad.Writer
import Data.Time

import MonaFormulaOperation
import MonaFormulaAntiprenex

import qualified Data.Map as Map
import qualified LazyDecisionProcedure as LDP
import qualified StrictDecisionProcedure as SDP
import qualified Logic as Lo
import qualified FormulaOperation as FO
import qualified Examples as Ex
import qualified MonaWrapper as MoWr
import qualified MonaParser as MoPa
import qualified BasicAutomata as BA
import qualified MonaSocket as MS


-- |Use Mona for translating formulas (so far only support for atoms)
-- to tree automata.
useMona = True

-- |Program arguments.
data ProgArgs =
  Validity FilePath
  | Antiprenex FilePath
  | Error


-- |Parse program arguments.
parseArgs :: [String] -> ProgArgs
parseArgs args
  | (length args) == 1 = Validity $ head args
  | (length args) == 2 && (last args) == "-p" = Antiprenex $ head args
  | otherwise = Error


-- |Show formula and its validity (strict approach)
showValid :: Lo.Formula -> IO ()
showValid f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ SDP.isValid f


-- |Show formula and its validity (lazy approach)
showValidLazy :: Lo.Formula -> IO ()
showValidLazy f = showValidMonaLazy [] f


-- |Show formula and its validity using MONA
showValidMonaLazy :: [(String, BA.WS2STreeAut)] -> Lo.Formula -> IO ()
showValidMonaLazy aut f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ LDP.isValid (Map.fromList aut) f


-- |Format validity answer
formatAnswer :: (Show a, Show b) => Either a b -> String
formatAnswer (Left x) = show x
formatAnswer (Right y) = "Error: " ++ show y


-- |Show formula and its simplicication for debug purposes.
formulaOperationsDebug :: Lo.Formula -> IO ()
formulaOperationsDebug f = do
  let sf = FO.simplifyFormula f in do
    putStrLn $ show $ FO.antiprenex sf
    putStrLn $ show $ FO.antiprenex $ FO.balanceFormula sf


-- |Main function
main = do
   args <- getArgs
   start <- getCurrentTime
   case (parseArgs args) of
     (Antiprenex file) -> do
       mona <- MoPa.parseFile file
       putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCallsFile mona
     (Validity file) -> do
       mona <- MoPa.parseFile file
       let prenexFile = antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCallsFile mona
           (hf, monareq) = runWriter $ Lo.convertMonaSub useMona $ MoWr.getBaseFormula prenexFile in
           do
             putStrLn $ show monareq
             auts <- MS.getMonaAutomata monareq
             showValidMonaLazy auts hf
     Error -> do
       prname <- getProgName
       putStrLn $ "Bad input params, file with WS2S formula required\n./" ++ prname ++ " [file]"
   stop <- getCurrentTime
   putStrLn $ "Time: " ++ show (diffUTCTime stop start)
