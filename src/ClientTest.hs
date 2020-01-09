import Data.Bits
import Network.Socket
import Network.BSD
import Data.List
import System.IO

-- main = do
--   h <- openConnection "localhost" 50889
--   hPutStrLn h


transferPath path = do
  h <- openConnection "127.0.0.1" "50889"
  hPutStrLn h path
  hFlush h
  str <- hGetLine h
  let num = read str :: Int
  putStrLn $ show num


stopServer = do
  h <- openConnection "127.0.0.1" "50889"
  hPutStrLn h "stop"


openConnection :: HostName -> String -> IO Handle
openConnection hostname port =
    do
       addrinfos <- getAddrInfo Nothing (Just hostname) (Just port)
       let serveraddr = head addrinfos
       sock <- socket (addrFamily serveraddr) Stream defaultProtocol

       -- Mark the socket for keep-alive handling since it may be idle
       -- for long periods of time
       --setSocketOption sock KeepAlive 1

       -- Connect to server
       connect sock (addrAddress serveraddr)

       -- Make a Handle out of it for convenience
       h <- socketToHandle sock ReadWriteMode

       -- We're going to set buffering to BlockBuffering and then
       -- explicitly call hFlush after each message, below, so that
       -- messages get logged immediately
       hSetBuffering h (BlockBuffering Nothing)

       -- Save off the socket, program name, and server address in a handle
       return $ h
