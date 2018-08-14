{-|
Module      : MonaParser
Description : Mona formulae parser
Author      : Vojtech Havlena, June 2018
License     : GPL-3
-}

module MonaAutomataParser where

import Control.Applicative ((<*))

import Data.List

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token

import qualified TreeAutomaton as TA
import qualified BasicAutomata as BA

type MonaState = Int
type MonaSymbol = String

data MonaTransition =
  MonaTransition [MonaState] MonaSymbol MonaState

data MonaGuide =
  MonaGuide String MonaState [MonaState]


instance Show MonaTransition where
  show (MonaTransition sts sym st) = "(" ++ show sts ++ ","++ sym ++") -> " ++ show st

instance Show MonaGuide where
  show (MonaGuide name src dest) = name ++ ": " ++ show src ++ " -> " ++ "(" ++ show dest ++ ")"


lexer = makeTokenParser emptyDef
m_comma = lexeme lexer (char ',')
m_lparen = lexeme lexer (char '(')
m_rparen = lexeme lexer (char ')')
m_ddot = lexeme lexer (char ':')
m_to = lexeme lexer (string "->")
m_white = whiteSpace lexer


m_eol :: Parser String
m_eol = try (string "\n\r")
  <|> string "\r\n"
  <|> string "\n"
  <|> string "\r"
  <?> "end of line"


parseString :: String -> [MonaGuide]
parseString str = case (parse parseGuideSet "MonaAutomataParser" str) of
  Left err   -> error $ show err
  Right res  -> res


parseTuple :: Parser String
parseTuple = many (noneOf ",->)(\n")


guideName :: Parser String
guideName = many (noneOf ":")


parseTransition :: Parser MonaTransition
parseTransition = do
  m_white
  m_lparen
  s <- sepBy parseTuple m_comma
  m_rparen
  m_to
  dest <- parseTuple
  return $ makeTransition (init s) (last s) dest


parseGuide :: Parser MonaGuide
parseGuide = do
  m_white
  name <- guideName
  m_ddot
  src <- parseTuple
  m_to
  m_lparen
  dst <- sepBy parseTuple m_comma
  m_rparen
  return $ makeGuide name src dst


parseTransitionSet :: Parser [MonaTransition]
parseTransitionSet = do
  trans <- many (try parseTransition)
  return trans


parseGuideSet :: Parser [MonaGuide]
parseGuideSet = do
  gds <- many (try parseGuide)
  return gds


toInt :: [String] -> [Int]
toInt = map (\a -> read a :: Int)


makeGuide :: String -> String -> [String] -> MonaGuide
makeGuide name src dest = MonaGuide name (read src :: Int) (toInt dest)


makeTransition :: [String] -> String -> String -> MonaTransition
makeTransition sts sym st = MonaTransition (toInt sts) sym (read st :: Int)
