{-|
Module      : MonaFormulaInfo
Description : Mona formulae information
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module MonaFormulaInfo where

import Data.List
import Data.Maybe
import MonaParser
import MonaFormulaOperationSubst

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Ord as Ord
import qualified Debug.Trace as Dbg

type FVType = Map.Map String Int

data FormulaFV = FormulaFV {
  global :: FVType
  , local :: FVType
  , preds :: [MonaDeclaration]
}


fvUpdateLocal :: FormulaFV -> String -> Int -> FormulaFV
fvUpdateLocal fv item val = FormulaFV (global fv) (Map.insert item val (local fv)) (preds fv)


fvUpdateLocPredVars :: FormulaFV -> [MonaMacroParam] -> FormulaFV
fvUpdateLocPredVars (FormulaFV gl lc pr) par = FormulaFV gl (Map.union (getMonaPredVars par) lc) pr


predsFV :: FormulaFV -> [String]
predsFV fv = concat $ map (getfv) (preds fv) where
  getfv (MonaDeclPred _ _ f) = freeVarsFormula f
  getfv (MonaDeclMacro _ _ f) = freeVarsFormula f


unionLocGlobFV :: FormulaFV -> FVType
unionLocGlobFV fv = Map.union (local fv) (global fv)


varsToDecls :: FVType -> [String]
varsToDecls fv = map (fvToDecl) $ Map.toList fv where
  fvToDecl (var, tp) = "var" ++ (show tp) ++ " " ++ var ++ ";"


formulaFVEmpty :: FormulaFV
formulaFVEmpty = FormulaFV Map.empty Map.empty []


getMonaVarDecls :: [MonaDeclaration] -> FVType
getMonaVarDecls = Map.fromList . concat . map (variableTypes) where
  variableTypes (MonaDeclVar0 ds) = map (\x -> (x, 0)) ds
  variableTypes (MonaDeclVar1 ds) = map (\(x,y) -> (x, 1)) ds
  variableTypes (MonaDeclVar2 ds) = map (\(x,y) -> (x, 2)) ds
  variableTypes _ = []


getMonaFormulaFV :: [MonaDeclaration] -> FormulaFV
getMonaFormulaFV d = FormulaFV (getMonaVarDecls d) (Map.empty) (filter (fltDec) d) where
  fltDec (MonaDeclPred _ _ _) = True
  fltDec (MonaDeclMacro _ _ _) = True
  fltDec _ = False


getMonaPredVars :: [MonaMacroParam] -> FVType
getMonaPredVars = Map.fromList . concat . map (variableTypes) where
  variableTypes (MonaMacroParamVar0 ds) = map (\x -> (x, 0)) ds
  variableTypes (MonaMacroParamVar1 ds) = map (\(x,y) -> (x, 1)) ds
  variableTypes (MonaMacroParamVar2 ds) = map (\(x,y) -> (x, 2)) ds
  variableTypes _ = []
