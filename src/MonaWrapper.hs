{-|
Module      : MonaWrapper
Description : Mona formulae wrapper
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaWrapper (
  getLogicFormula
  , getFormulas
) where

import Data.List
import Data.Maybe

import MonaParser
import MonaFormulaOperation
import MonaFormulaAntiprenex

import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


-- |Convert Mona formula to Base Mona formula (without Ext1 quatifiers, only
-- basic logical connectives, ...).
convert2Base :: MonaFormula -> MonaFormula
convert2Base t@(MonaFormulaEx1 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaEx2 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaAll1 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaAll2 _ _) = unwindQuantif t
convert2Base (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
convert2Base (MonaFormulaImpl f1 f2) = MonaFormulaDisj (MonaFormulaNeg $ convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaConj f1 f2) = MonaFormulaConj (convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaDisj f1 f2) = MonaFormulaDisj (convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaNeg f) = MonaFormulaNeg $ convert2Base f
convert2Base t = error $ "convert2Base: Unimplemented: " ++ (show t) -- TODO: Complete


-- |Unwind several chained quatifiers to chain of quatifiers (i.e.
-- Forall X1, X2 ---> Forall X1, Forall X2). Replace first order quatifiers as well.
unwindQuantif :: MonaFormula -> MonaFormula
-- unwindQuantif (MoPa.MonaFormulaEx1 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaEx1 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MonaFormulaEx1 [x] f) = MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaEx1 (x:xs) f) = MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MonaFormulaEx2 xs f))
unwindQuantif (MonaFormulaEx2 [x] f) = MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaEx2 (x:xs) f) = MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MonaFormulaEx2 xs f))
-- unwindQuantif (MoPa.MonaFormulaAll1 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaAll1 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MonaFormulaAll1 [x] f) = MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaAll1 (x:xs) f) = MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MonaFormulaAll2 xs f))

unwindQuantif (MonaFormulaAll2 [x] f) = MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaAll2 (x:xs) f) = MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MonaFormulaAll2 xs f))
unwindQuantif t = error $ "Unimplemented: " ++ (show t) -- TODO: Complete


-- |Hanle Mona variables declarations.
handleWhere :: (String, Maybe MonaFormula) -> (String, Maybe MonaFormula)
handleWhere = id


-- |Get Mona formulas from Mona file.
getFormulas :: MonaFile -> [MonaFormula]
getFormulas file = map (\(MonaDeclFormula f) -> f) $ filter (declFilter) (mf_decls file) where
   declFilter (MonaDeclFormula _) = True
   declFilter _ = False


-- |Parse Mona atom -- atoms are stored as strings.
parseAtom :: String -> Maybe Lo.Atom
parseAtom atom = parseSimpleAtom $ words atom


-- |Parse atom from a list containig 3 items [op1, operator, op2].
parseSimpleAtom :: [String] ->  Maybe Lo.Atom
parseSimpleAtom arr =
   if (length arr) /= 3 then Nothing
   else case arr !! 1 of
      "sing" -> Just $ Lo.Sing $ arr !! 2
      "sub" -> Just $ Lo.Subseteq (arr !! 0) (arr !! 2)
      --"cat1" -> Just $ Lo.Cat1 (arr !! 0) (arr !! 2)
      "eps" -> Just $ Lo.Eps $ arr !! 2
      "in" -> Just $ Lo.In (arr !! 0) (arr !! 2)
      "~=" -> Just $ Lo.Neq (arr !! 0) (arr !! 2)
      "=" -> Just $ Lo.Eqn (arr !! 0) (arr !! 2)
      "=.1" -> Just $ Lo.Cat2 (arr !! 0) (arr !! 2)
      "=.0" -> Just $ Lo.Cat1 (arr !! 0) (arr !! 2)


-- |Convert Mona string containing atom to Logic.Atom
convertAtom :: MonaAtom -> Lo.Atom
convertAtom _ = Lo.Sing "X"
-- convertAtom atom = case (parseAtom atom) of
--    Nothing -> error $ "Parse error" ++ (show atom)
--    Just res -> res


-- |Convert Mona base formula to Logic.Formula
convertBase2Simple :: MonaFormula -> Lo.Formula
convertBase2Simple (MonaFormulaAll2 [p] f) = Lo.ForAll (fst p) (convertBase2Simple f)
convertBase2Simple (MonaFormulaEx2 [p] f) = Lo.Exists (fst p) (convertBase2Simple f)
convertBase2Simple (MonaFormulaDisj f1 f2) = Lo.Disj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MonaFormulaConj f1 f2) = Lo.Conj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MonaFormulaNeg f) = Lo.Neg $ convertBase2Simple f
convertBase2Simple (MonaFormulaAtomic atom) = Lo.FormulaAtomic $ convertAtom atom
convertBase2Simple t = error $ "Unimplemented: " ++ (show t)  -- TODO: Complete


getLogicFormula :: MonaFormula -> Lo.Formula
getLogicFormula = convertBase2Simple . convert2Base


loadFormulas p = do
   file <- parseFile p
   let formulas = getFormulas file in
      putStrLn $ show $ convertBase2Simple $ convert2Base $ head formulas


flatTest file = do
  mona <- parseFile file
  putStrLn $ show mona
  putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCallsFile mona
