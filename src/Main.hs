
import qualified DecisionProcedure as DP
import qualified Logic as Lo


-- |Examples of WSkS formulas.
exampleFormula0 = Lo.Exists "X" (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X")))
exampleFormula1 = Lo.Neg (Lo.Exists "X" (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))))
exampleFormula2 = Lo.Exists "X" (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "X")) ( Lo.Exists "Y" (Lo.FormulaAtomic (Lo.Cat "X" "Y"))))
exampleFormula3 = Lo.Exists "X" (Lo.Conj (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))) (Lo.FormulaAtomic (Lo.Sing "X")))
exampleFormula4 = Lo.Exists "X" (Lo.Exists "Y" (Lo.FormulaAtomic (Lo.Subseteq "X" "Y")))
exampleFormula5 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.FormulaAtomic (Lo.Eps "X")) (Lo.FormulaAtomic (Lo.Subseteq "X" "Y"))))
exampleFormula6 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.Conj (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "Y")) (Lo.Neg (Lo.FormulaAtomic (Lo.Eps "Y"))))  (Lo.FormulaAtomic (Lo.Eps "X"))) (Lo.FormulaAtomic (Lo.Subseteq "Y" "X"))))
exampleFormula7 = Lo.Exists "X" (Lo.Exists "Y" (Lo.Conj (Lo.Conj (Lo.FormulaAtomic (Lo.Eps "X")) (Lo.Neg (Lo.FormulaAtomic (Lo.Eps "X")))) (Lo.FormulaAtomic (Lo.Subseteq "X" "Y"))))

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

main = showValidLazy exampleFormula7
