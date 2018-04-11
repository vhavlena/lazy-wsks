{-|
Module      : MonaWrapper
Description : Mona formulae wrapper
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaWrapper where

import qualified MonaParser as MoPa
import qualified Logic as Lo


convert2Base :: MoPa.MonaFormula -> MoPa.MonaFormula
convert2Base t@(MoPa.MonaFormulaEx1 var f) = unwindVars t
convert2Base t@(MoPa.MonaFormulaEx2 var f) = unwindVars t
convert2Base t@(MoPa.MonaFormulaAll1 var f) = unwindVars t
convert2Base t@(MoPa.MonaFormulaAll2 var f) = unwindVars t
convert2Base (MoPa.MonaFormulaAtomic atom) = MoPa.MonaFormulaAtomic atom
convert2Base (MoPa.MonaFormulaImpl f1 f2) = MoPa.MonaFormulaDisj (MoPa.MonaFormulaNeg (convert2Base f1)) (convert2Base f2)

unwindVars (MoPa.MonaFormulaEx1 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "Sing "++ (fst x) ++ " term")))
unwindVars (MoPa.MonaFormulaEx1 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindVars (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "Sing "++ (fst x) ++ " term")))
unwindVars (MoPa.MonaFormulaAll1 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "Sing "++ (fst x) ++ " term")))
unwindVars (MoPa.MonaFormulaAll1 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindVars (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "Sing "++ (fst x) ++ " term")))
unwindVars (MoPa.MonaFormulaAll2 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindVars (MoPa.MonaFormulaAll2 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (unwindVars (MoPa.MonaFormulaAll2 xs f))
unwindVars (MoPa.MonaFormulaEx2 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindVars (MoPa.MonaFormulaEx2 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (unwindVars (MoPa.MonaFormulaEx2 xs f))


handleWhere :: (String, Maybe MoPa.MonaFormula) -> (String, Maybe MoPa.MonaFormula)
handleWhere = id

getFormulas :: MoPa.MonaFile -> [MoPa.MonaFormula]
getFormulas file = map (\(MoPa.MonaDeclFormula f) -> f) $ filter (declFilter) (MoPa.mf_decls file) where
   declFilter (MoPa.MonaDeclFormula _) = True
   declFilter _ = False

loadFormulas p = do
   file <- MoPa.parseFile p
   let formulas = getFormulas file in
      putStrLn $ show $ convert2Base $ head formulas
