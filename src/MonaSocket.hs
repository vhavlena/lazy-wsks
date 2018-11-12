{-|
Module      : MonaSocket
Description : Module for communication with Mona.
Author      : Vojtech Havlena, August 2018
License     : GPL-3
-}

module MonaSocket (
  getMonaAutomata
  , getAutFormulaMona
) where

import System.IO.Temp
import GHC.IO.Handle
import System.Process
import Data.List

import MonaFormulaOperation
import MonaParser
import qualified MonaAutomataParser as MAP
import MonaAutomataWrapper
import TreeAutomaton
import BasicAutomata
import qualified Logic as Lo
import qualified Alphabet as Alp


-- |Create a temporary file to store mona formula.
-- dir: directory where tmp file is created
-- name: name of a teporary file
-- str: string contains formula in mona format
writeTmpMonaFile :: FilePath -> String -> String -> IO WS2STreeAut
writeTmpMonaFile dir name str = do
   res <- withTempFile dir name (monaActionAut str)
   return $ removeUnreachable $ monaGTAToTA $ MAP.parseString res


-- |Get Mona tree automaton corresponding to a given formula with a given
-- free variables.
getAutFormulaMona :: [Lo.Var] -> Lo.Formula -> IO WS2STreeAut
getAutFormulaMona vars fle = writeTmpMonaFile "" "tmp-mona-34F53DSW4.mona" monafle where
  monafle = "ws2s;\n" ++ decl ++ Lo.showFormulaMona fle ++ ";"
  decl = "var1 " ++ (intercalate "," var1) ++ ";\nvar2 " ++ (intercalate "," var2) ++ ";\n"
  (var1, var2) = getVariableDeclaration vars fle


getVariableDeclaration :: [Lo.Var] -> Lo.Formula -> ([Lo.Var], [Lo.Var])
getVariableDeclaration vars (Lo.FormulaAtomic (Lo.MonaAt atom _)) = getMonaAtomVars atom vars


getMonaAtomVars :: MonaAtom -> [Lo.Var] -> ([Lo.Var], [Lo.Var])
getMonaAtomVars (MonaAtomLe a1 a2) vars = (vars, [])
getMonaAtomVars (MonaAtomLeq a1 a2) vars = getMonaAtomVars (MonaAtomLe a1 a2) vars
getMonaAtomVars (MonaAtomGeq a1 a2) vars = getMonaAtomVars (MonaAtomLe a1 a2) vars
getMonaAtomVars (MonaAtomGe a1 a2) vars = getMonaAtomVars (MonaAtomLe a1 a2) vars
getMonaAtomVars (MonaAtomIn a1 a2) vars = (fv, vars \\ fv) where
  fv = freeVarsTerm a1
getMonaAtomVars t vars = ([], vars)


-- |Get Mona tree automata for a list of tuples (identifier, formula) ->
-- (identifier, corresponding mona TA).
getMonaAutomata :: [(String, Lo.Formula)] -> IO [(String, WS2STreeAut)]
getMonaAutomata lst = sequence $ zipWith (conn) lst $ map (conv) lst where
  conv (_, fle) = getAutFormulaMona (Lo.freeVars fle) fle
  conn (iden, fle) aut = aut >>= \x -> return (iden,x)


-- |Temporary file action. Write a given string into a temporary file and
-- then run Mona on this tmp file.
monaActionAut :: String -> FilePath -> Handle -> IO String
monaActionAut str filename handle = do
  putStrLn str
  hPutStr handle str
  hFlush handle
  hClose handle
  res <- readProcess "mona" ["-q","-w","-n",filename] []
  return res
