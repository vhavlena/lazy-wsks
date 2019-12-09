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
) where

import System.IO
import System.IO.Unsafe
import System.Process

import MonaParser
import AuxFunctions
import qualified Data.List as Lst
import qualified Data.Map as Map

type DeclSize = Map.Map String Int

tmpFileName = "_tmp_size.mona"
tmpDeclsFileName = "_tmp_decls_.data"
sizeEstScript = "./EstimationTest.py"

-- |Get predicates sizes (assumes that predicates/macros contain no call to
-- other macros/predicates --> the predicates are flat)
getPredSizes :: MonaFile -> IO DeclSize
getPredSizes (MonaFile _ decls) = do
  lst <- sequence $ map (estScriptWrap) predFormulas
  return $ Map.fromList lst
    where
      estScriptWrap (MonaDeclMacro nm _ fl) = (callEstScript fl) >>= \y -> return (nm,y)
      estScriptWrap (MonaDeclPred nm _ fl) = (callEstScript fl) >>= \y -> return (nm,y)
      predFormulas = filter (fltPred) decls
      fltPred (MonaDeclMacro _ _ _) = True
      fltPred (MonaDeclPred _ _ _) = True
      fltPred _ = False


-- |Call a script for formula size estimation
callEstScript :: MonaFormula -> IO Int
callEstScript f = do
  writeFile tmpFileName (show f)
  out <- readProcess sizeEstScript [tmpFileName] []
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
callEstScriptPure :: MonaFormula -> Int
callEstScriptPure = unsafePerformIO . callEstScript
