
module MonaSocket where

import System.IO.Temp
import GHC.IO.Handle
import System.Process

import MonaAutomataParser
import MonaAutomataWrapper
import TreeAutomaton
import qualified Logic as Lo

writeTmpMonaFile :: FilePath -> String -> String -> IO (BATreeAutomaton MonaState Alp.Symbol)
writeTmpMonaFile dir name str = do
   res <- withTempFile dir name (monaActionAut str)
   return $ monaGTAToTA $ parseString res

getAutAtomMona :: [Lo.Variable] -> Lo.Atom -> BATreeAutomaton MonaState Alp.Symbol


monaActionAut :: String -> FilePath -> Handle -> IO String
monaActionAut str filename handle = do
  hPutStr handle str
  hFlush handle
  hClose handle
  res <- readProcess "mona" ["-q","-w","-n",filename] []
  return res
