{-|
Module      : FormulaSizeEstimation
Description : Mona formulae size estimation.
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module FormulaSizeEstimation (
  callEstScriptPure
  , callEstScript
  , formatPredSizes
  , writePredSizes
  , writePredicateTemplate
  , transferPath
  , stopServer
  , deleteTmpFiles
) where

import System.IO
import System.IO.Unsafe
import System.Process
import Network.Socket
import System.Directory
import qualified System.IO.Strict as SIO
import System.Random

import MonaFormula
import AuxFunctions
import MonaFormulaInfo
import MonaFormulaOperationSubst
import qualified Data.List as Lst
import qualified Data.Map as Map
import qualified Data.Set as Set

type DeclSize = Map.Map String Integer

tmpFolder = "tmpSizes/"
tmpFileName = tmpFolder ++ "_tmp_size.mona"
tmpDeclsFileName = "_tmp_decls_.data"
sizeEstScript = "./../external/predict.py"
predMonaPath = "../../predict_mona/executables/bin/mona"


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
callEstScript :: FormulaFV -> String -> MonaFormula -> IO Integer
callEstScript fv suff f = do
  num <- randomIO :: IO Int
  i <- SIO.run $ callEstScript' fv (suff++(show num)) f
  out <- transferPath (tmpFileName ++ suff ++ (show num))
  return $ parseOutput out
  where
    callEstScript' :: FormulaFV -> String -> MonaFormula -> SIO.SIO Int
    callEstScript' fv suff f = do
    declContent <- SIO.readFile tmpDeclsFileName
    let fvDecls = Set.fromList $ predsFV fv
    let freevars = Set.fromList $ freeVarsFormula f
    let fvintGlobal = Map.filterWithKey (\k _ -> Set.member k fvDecls) (global fv)
    let fvintLocal = Map.filterWithKey (\k _ -> Set.member k freevars) (unionLocGlobFV fv)
    let varDecl = unlines $ varsToDecls (Map.union fvintLocal fvintGlobal)
    let lins = lines declContent
    let header = lins !! 0
    let decls = unlines $ tail lins
    let content = header ++ "\n" ++ varDecl ++ decls ++ (show f) ++ ";"
    SIO.writeFile (tmpFileName ++ suff) content
    SIO.return' 5



-- |Write sizes of predicates to the tmp file
writePredSizes :: DeclSize -> IO ()
writePredSizes dict = writeFile tmpDeclsFileName (formatPredSizes dict)


-- |Format dictionary of predicate sizes for output
formatPredSizes :: DeclSize -> String
formatPredSizes dict = Lst.intercalate "\n" $ map (formatPair) $ Map.toList dict where
  formatPair (name,val) = (show name) ++ ": " ++ (show val)


-- |Parse estimation script output
parseOutput :: String -> Integer
parseOutput str = read str :: Integer


-- |Call estimation script PURELY (assumes that the script behaves as a mapping)
callEstScriptPure :: FormulaFV -> String -> MonaFormula -> Integer
callEstScriptPure fv suff = unsafePerformIO . callEstScript fv suff


transferPath path = do
  h <- openConnection "127.0.0.1" "50889"
  hPutStrLn h path
  hFlush h
  str <- hGetLine h
  hClose h
  return str


stopServer = do
  h <- openConnection "127.0.0.1" "50889"
  hPutStrLn h "stop"
  hClose h


openConnection :: HostName -> String -> IO Handle
openConnection hostname port = do
  addrinfos <- getAddrInfo Nothing (Just hostname) (Just port)
  let serverAddr = head addrinfos
  sock <- socket (addrFamily serverAddr) Stream defaultProtocol
  connect sock (addrAddress serverAddr)
  h <- socketToHandle sock ReadWriteMode
  hSetBuffering h (BlockBuffering Nothing)
  return h


deleteTmpFiles :: IO ()
deleteTmpFiles = do
  files <- listDirectory tmpFolder
  sequence_ $ map (\x -> removeFile (tmpFolder ++ x)) files
