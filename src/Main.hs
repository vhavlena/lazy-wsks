{-|
Module      : Main
Description : Main file for WSkS decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

import System.Environment
import Data.Time

import qualified LazyDecisionProcedure as LDP
import qualified StrictDecisionProcedure as SDP
import qualified Logic as Lo
import qualified FormulaOperation as FO
import qualified Examples as Ex
import qualified MonaWrapper as MoWr
import qualified MonaParser as MoPa


-- |Show formula and its validity (strict approach)
showValid :: Lo.Formula -> IO ()
showValid f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ SDP.isValid f


-- |Show formula and its validity (lazy approach)
showValidLazy :: Lo.Formula -> IO ()
showValidLazy f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ LDP.isValid f


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
   if (length args) /= 1 then do
     prname <- getProgName
     putStrLn $ "Bad input params, file with WS2S formula required\n./" ++ prname ++ " [file]"
   else do
      start <- getCurrentTime
      file <- MoPa.parseFile $ head args
      let formulas = MoWr.getFormulas file
          hf = Lo.convertToBaseFormula $ MoWr.getLogicFormula $ head formulas in
          --formulaOperationsDebug $ hf
          showValidLazy $ FO.simplifyFormula $ FO.antiprenex $ FO.balanceFormula $ FO.simplifyFormula $ hf
      stop <- getCurrentTime
      putStrLn $ "Time: " ++ show (diffUTCTime stop start)
