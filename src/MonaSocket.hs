
module MonaSocket where

import System.IO.Temp
import GHC.IO.Handle
import System.Process
import Data.List

import MonaAutomataParser
import MonaAutomataWrapper
import TreeAutomaton
import BasicAutomata
import qualified Logic as Lo
import qualified Alphabet as Alp


writeTmpMonaFile :: FilePath -> String -> String -> IO WS2STreeAut
writeTmpMonaFile dir name str = do
   res <- withTempFile dir name (monaActionAut str)
   return $ monaGTAToTA $ parseString res


getAutFormulaMona :: [Lo.Var] -> Lo.Formula -> IO WS2STreeAut
getAutFormulaMona vars fle = writeTmpMonaFile "" "tmp-mona-34F53DSW4.mona" monafle where
  monafle = "ws2s;\nvar2 " ++ (intercalate "," vars) ++ ";\n" ++ Lo.showFormulaMona fle ++ ";"


getMonaAutomata :: [(String, Lo.Formula)] -> IO [(String, WS2STreeAut)]
getMonaAutomata lst = sequence $ zipWith (conn) lst $ map (conv) lst where
  conv (iden, fle) = getAutFormulaMona (Lo.freeVars fle) fle
  conn (iden, fle) aut = aut >>= \x -> return (iden,x)


monaActionAut :: String -> FilePath -> Handle -> IO String
monaActionAut str filename handle = do
  hPutStr handle str
  hFlush handle
  hClose handle
  res <- readProcess "mona" ["-q","-w","-n",filename] []
  return res
