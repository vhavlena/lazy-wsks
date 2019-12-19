{-|
Module      : FormulaSizeEstimation
Description : Mona formulae size estimation.
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module FormulaSizeEstimation (
  getPredSizes
  , callEstScriptPure
  , callEstScript
  , formatPredSizes
  , writePredSizes
  , writePredicateTemplate
) where

import System.IO
import System.IO.Unsafe
import System.Process

import MonaParser
import AuxFunctions
import MonaFormulaInfo
import MonaFormulaOperationSubst
import qualified Data.List as Lst
import qualified Data.Map as Map
import qualified Data.Set as Set

type DeclSize = Map.Map String Int

tmpFileName = "_tmp_size.mona"
tmpDeclsFileName = "_tmp_decls_.data"
sizeEstScript = "./../external/predict.py"
predMonaPath = "../../predict_mona/executables/bin/mona"

-- |Get predicates sizes (assumes that predicates/macros contain no call to
-- other macros/predicates --> the predicates are flat)
getPredSizes :: MonaFile -> IO DeclSize
getPredSizes (MonaFile _ decls) = do
  lst <- sequence $ map (estScriptWrap) predFormulas
  return $ Map.fromList lst
    where
      fv = getMonaVarDecls decls
      estScriptWrap (MonaDeclMacro nm _ fl) = (callEstScript fv fl) >>= \y -> return (nm,y)
      estScriptWrap (MonaDeclPred nm _ fl) = (callEstScript fv fl) >>= \y -> return (nm,y)
      predFormulas = filter (fltPred) decls
      fltPred (MonaDeclMacro _ _ _) = True
      fltPred (MonaDeclPred _ _ _) = True
      fltPred _ = False


writePredicateTemplate :: MonaFile -> IO ()
writePredicateTemplate (MonaFile header decls) = do
  writeFile tmpDeclsFileName (hstr ++ "\n" ++ fstr)
    where
      hstr = case header of Just x -> x ++ ";"
                            Nothing -> ""
      fstr = unlines $ map (\x -> (show x) ++ ";") $ predFormulas
      predFormulas = filter (fltPred) decls
      fltPred (MonaDeclMacro _ _ _) = True
      fltPred (MonaDeclPred _ _ _) = True
      fltPred _ = False


-- |Call a script for formula size estimation
callEstScript :: FVType -> MonaFormula -> IO Int
callEstScript fv f = do
  declContent <- readFile tmpDeclsFileName
  let freevars = Set.fromList $ freeVarsFormula f
  let fvint = Map.filterWithKey (\k _ -> Set.member k freevars) fv
  let varDecl = unlines $ varsToDecls fvint
  let lins = lines declContent
  let header = lins !! 0
  let decls = unlines $ tail lins
  let content = header ++ "\n" ++ varDecl ++ decls ++ (show f) ++ ";"
  writeFile tmpFileName content
  out <- readProcess sizeEstScript [predMonaPath, tmpFileName] []
  return $ parseOutput out


-- |Write sizes of predicates to the tmp file
writePredSizes :: DeclSize -> IO ()
writePredSizes dict = writeFile tmpDeclsFileName (formatPredSizes dict)


-- |Format dictionary of predicate sizes for output
formatPredSizes :: DeclSize -> String
formatPredSizes dict = Lst.intercalate "\n" $ map (formatPair) $ Map.toList dict where
  formatPair (name,val) = (show name) ++ ": " ++ (show val)


-- |Parse estimation script output
parseOutput :: String -> Int
parseOutput str = read str :: Int


-- |Call estimation script PURELY (assumes that the script behaves as a mapping)
callEstScriptPure :: FVType -> MonaFormula -> Int
callEstScriptPure fv = unsafePerformIO . callEstScript fv
