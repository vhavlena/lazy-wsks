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

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token
import Control.Applicative ((<*))

import qualified MonaParser as MoPa
import qualified Logic as Lo


-- |Convert Mona formula to Base Mona formula (without Ext1 quatifiers, only
-- basic logical connectives, ...).
convert2Base :: MoPa.MonaFormula -> MoPa.MonaFormula
convert2Base t@(MoPa.MonaFormulaEx1 var f) = unwindQuantif t
convert2Base t@(MoPa.MonaFormulaEx2 var f) = unwindQuantif t
convert2Base t@(MoPa.MonaFormulaAll1 var f) = unwindQuantif t
convert2Base t@(MoPa.MonaFormulaAll2 var f) = unwindQuantif t
convert2Base (MoPa.MonaFormulaAtomic atom) = MoPa.MonaFormulaAtomic atom
convert2Base (MoPa.MonaFormulaImpl f1 f2) = MoPa.MonaFormulaDisj (MoPa.MonaFormulaNeg (convert2Base f1)) (convert2Base f2)
convert2Base (MoPa.MonaFormulaConj f1 f2) = MoPa.MonaFormulaConj (convert2Base f1) (convert2Base f2)
convert2Base (MoPa.MonaFormulaNeg f) = MoPa.MonaFormulaNeg (convert2Base f)
convert2Base t = error $ "Unimplemented: " ++ (show t) -- TODO: Complete


-- |Unwind several chained quatifiers to chain of quatifiers (i.e.
-- Forall X1, X2 ---> Forall X1, Forall X2). Replace first order quatifiers as well.
unwindQuantif :: MoPa.MonaFormula -> MoPa.MonaFormula
-- unwindQuantif (MoPa.MonaFormulaEx1 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaEx1 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MoPa.MonaFormulaEx1 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MoPa.MonaFormulaEx1 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MoPa.MonaFormulaEx2 xs f))
unwindQuantif (MoPa.MonaFormulaEx2 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MoPa.MonaFormulaEx2 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MoPa.MonaFormulaEx2 xs f))
-- unwindQuantif (MoPa.MonaFormulaAll1 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaAll1 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MoPa.MonaFormulaAll1 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MoPa.MonaFormulaAll1 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MoPa.MonaFormulaAll2 xs f))

unwindQuantif (MoPa.MonaFormulaAll2 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MoPa.MonaFormulaAll2 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MoPa.MonaFormulaAll2 xs f))
unwindQuantif t = error $ "Unimplemented: " ++ (show t) -- TODO: Complete

-- |Hanle Mona variables declarations.
handleWhere :: (String, Maybe MoPa.MonaFormula) -> (String, Maybe MoPa.MonaFormula)
handleWhere = id


-- |Get Mona formulas from Mona file.
getFormulas :: MoPa.MonaFile -> [MoPa.MonaFormula]
getFormulas file = map (\(MoPa.MonaDeclFormula f) -> f) $ filter (declFilter) (MoPa.mf_decls file) where
   declFilter (MoPa.MonaDeclFormula _) = True
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
      "cat1" -> Just $ Lo.Cat1 (arr !! 0) (arr !! 2)
      "eps" -> Just $ Lo.Eps $ arr !! 2
      "in" -> Just $ Lo.In (arr !! 0) (arr !! 2)
      "~=" -> Just $ Lo.Neq (arr !! 0) (arr !! 2)
      "=" -> Just $ Lo.Eqn (arr !! 0) (arr !! 2)


-- |Convert Mona string containing atom to Logic.Atom
convertAtom :: String -> Lo.Atom
convertAtom atom = case (parseAtom atom) of
   Nothing   -> error $ "Parse error" ++ (show atom)
   Just res -> res


-- |Convert Mona base formula to Logic.Formula
convertBase2Simple :: MoPa.MonaFormula -> Lo.Formula
convertBase2Simple (MoPa.MonaFormulaAll2 [p] f) = Lo.ForAll (fst p) (convertBase2Simple f)
convertBase2Simple (MoPa.MonaFormulaEx2 [p] f) = Lo.Exists (fst p) (convertBase2Simple f)
convertBase2Simple (MoPa.MonaFormulaDisj f1 f2) = Lo.Disj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MoPa.MonaFormulaConj f1 f2) = Lo.Conj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MoPa.MonaFormulaNeg f) = Lo.Neg (convertBase2Simple f)
convertBase2Simple (MoPa.MonaFormulaAtomic atom) = Lo.FormulaAtomic (convertAtom atom)
convertBase2Simple t = error $ "Unimplemented: " ++ (show t)  -- TODO: Complete


getLogicFormula :: MoPa.MonaFormula -> Lo.Formula
getLogicFormula = convertBase2Simple . convert2Base

loadFormulas p = do
   file <- MoPa.parseFile p
   let formulas = getFormulas file in
      putStrLn $ show $ convertBase2Simple $ convert2Base $ head formulas
