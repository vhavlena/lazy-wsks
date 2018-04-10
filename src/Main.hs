
import qualified DecisionProcedure as DP
import qualified Logic as Lo
import qualified Examples as Ex


-- |Show formula and its validity
showValid :: Lo.Formula -> IO ()
showValid f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ DP.isValid f


showValidLazy :: Lo.Formula -> IO ()
showValidLazy f = do
   putStrLn $ show f
   putStrLn $ formatAnswer $ DP.isValidLazy f


-- |Format validity answer
formatAnswer :: (Show a, Show b) => Either a b -> String
formatAnswer (Left x) = show x
formatAnswer (Right y) = "Error: " ++ show y

main = showValidLazy Ex.exampleFormula8
