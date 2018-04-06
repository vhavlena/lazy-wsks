
import qualified DecisionProcedure as DP
import qualified Logic as Lo


-- |Examples of WSkS formulas.
exampleFormula1 = Lo.Neg (Lo.Exists "X" (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))))
exampleFormula2 = Lo.Exists "X" (Lo.Conj (Lo.FormulaAtomic (Lo.Sing "X")) ( Lo.Exists "Y" (Lo.FormulaAtomic (Lo.Cat "X" "Y"))))
exampleFormula3 = Lo.Exists "X" (Lo.Conj (Lo.Neg (Lo.FormulaAtomic (Lo.Sing "X"))) (Lo.FormulaAtomic (Lo.Sing "X")))


-- |Show formula and its validity
showValid :: Lo.Formula -> IO ()
showValid f = do
   putStrLn $ show f
   putStrLn $ show $ DP.isValid exampleFormula3


main = showValid exampleFormula3
