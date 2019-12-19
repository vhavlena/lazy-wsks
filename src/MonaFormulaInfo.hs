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

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Ord as Ord
import qualified Debug.Trace as Dbg

type FVType = Map.Map String Int


varsToDecls :: FVType -> [String]
varsToDecls fv = map (fvToDecl) $ Map.toList fv where
  fvToDecl (var, tp) = "var" ++ (show tp) ++ " " ++ var ++ ";"


getMonaVarDecls :: [MonaDeclaration] -> FVType
getMonaVarDecls = Map.fromList . concat . map (variableTypes) where
  variableTypes (MonaDeclVar0 ds) = map (\x -> (x, 0)) ds
  variableTypes (MonaDeclVar1 ds) = map (\(x,y) -> (x, 1)) ds
  variableTypes (MonaDeclVar2 ds) = map (\(x,y) -> (x, 2)) ds
  variableTypes _ = []


getMonaPredVars :: [MonaMacroParam] -> FVType
getMonaPredVars = Map.fromList . concat . map (variableTypes) where
  variableTypes (MonaMacroParamVar0 ds) = map (\x -> (x, 0)) ds
  variableTypes (MonaMacroParamVar1 ds) = map (\(x,y) -> (x, 1)) ds
  variableTypes (MonaMacroParamVar2 ds) = map (\(x,y) -> (x, 2)) ds
  variableTypes _ = []
