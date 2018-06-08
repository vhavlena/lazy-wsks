
import System.Environment

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
   if (length args) /= 1 then putStrLn "Bad input params, file with formula required"
   else do
      file <- MoPa.parseFile $ head args
      let formulas = MoWr.getFormulas file
          hf = Lo.convertToBaseFormula $ MoWr.getLogicFormula $ head formulas in
          --formulaOperationsDebug $ hf
          showValidLazy $ FO.simplifyFormula $ FO.antiprenex $ FO.balanceFormula $ FO.simplifyFormula $ hf
