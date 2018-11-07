{-|
Module      : MonaWrapper
Description : Mona formulae wrapper
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaWrapper (
  getBaseFormula
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


-- |Convert Mona string containing atom to Logic.Atom
convertAtom :: MonaAtom -> Lo.Atom
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermCat (MonaTermVar v2) (MonaTermConst 0))) = Lo.Cat1 v1 v2
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermCat (MonaTermVar v2) (MonaTermConst 1))) = Lo.Cat2 v1 v2
convertAtom (MonaAtomEq (MonaTermVar v1) (MonaTermVar v2)) = Lo.Eqn v1 v2
convertAtom (MonaAtomNeq (MonaTermVar v1) (MonaTermVar v2)) = Lo.Neq v1 v2
convertAtom (MonaAtomIn (MonaTermVar v1) (MonaTermVar v2)) = Lo.Subseteq v1 v2
convertAtom (MonaAtomSub (MonaTermVar v1) (MonaTermVar v2)) = Lo.Subseteq v1 v2
convertAtom (MonaAtomSing (MonaTermVar v)) = Lo.Sing v
convertAtom (MonaAtomEps (MonaTermVar v)) = Lo.Eps v
convertAtom a = error $ "convertAtom: Unsupported behaviour: " ++ (show a)


convertBaseMonaToFormula :: MonaFormula -> Lo.Formula
convertBaseMonaToFormula (MonaFormulaAtomic atom) = Lo.FormulaAtomic $ convertAtom atom
convertBaseMonaToFormula (MonaFormulaDisj f1 f2) = Lo.Disj (convertBaseMonaToFormula f1) (convertBaseMonaToFormula f2)
convertBaseMonaToFormula (MonaFormulaConj f1 f2) = Lo.Conj (convertBaseMonaToFormula f1) (convertBaseMonaToFormula f2)
convertBaseMonaToFormula (MonaFormulaNeg f) = Lo.Neg $ convertBaseMonaToFormula f
convertBaseMonaToFormula (MonaFormulaEx1 [p] f) = Lo.Exists var $ Lo.Conj (convertBaseMonaToFormula f) (Lo.FormulaAtomic $ Lo.Sing var) where
  var = fst p
convertBaseMonaToFormula (MonaFormulaEx2 [p] f) = Lo.Exists (fst p) (convertBaseMonaToFormula f)
convertBaseMonaToFormula f = error $ "convertBaseMonaToFormula: Unsupported behaviour: " ++ (show f)


getBaseFormula :: MonaFile -> Lo.Formula
getBaseFormula (MonaFile dom decls) = convertBaseMonaToFormula fle where
  (MonaDeclFormula fle) = head $ filter (flt) decls
  flt (MonaDeclFormula f) = True
  flt _ = False



flatTest file = do
  mona <- parseFile file
  putStrLn $ show mona
  putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCallsFile mona
