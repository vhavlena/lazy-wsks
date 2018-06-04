
import System.Environment

import qualified LazyDecisionProcedure as LDP
import qualified StrictDecisionProcedure as SDP
import qualified Logic as Lo
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


-- |Main function
main = do
   args <- getArgs
   if (length args) /= 1 then putStrLn "Bad input params, file with formula required"
   else do
      file <- MoPa.parseFile $ head args
      let formulas = MoWr.getFormulas file in
         showValidLazy $ Lo.antiprenex $ Lo.removeForAll $ MoWr.getLogicFormula $ head formulas
