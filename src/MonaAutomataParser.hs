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

data MonaGuideRule =
  MonaGuideRule String MonaState [MonaState]


data MonaGuide = MonaGuide [MonaGuideRule] deriving (Show)

data MonaStateSpace = MonaStateSpace {
  iden :: MonaState
  , name :: String
  , size :: Int
  , initial :: MonaState
  , transitions :: [MonaTransition]
} deriving (Show)


data MonaGTAHeader = MonaGTAHeader {
  variables :: [String]
  , accept :: [MonaState]
  , reject :: [MonaState]
} deriving (Show)


data MonaGTA = MonaGTA {
  header :: MonaGTAHeader
  , guide :: MonaGuide
  , spaces :: [MonaStateSpace]
} deriving (Show)


instance Show MonaTransition where
  show (MonaTransition sts sym st) = "(" ++ show sts ++ ","++ sym ++") -> " ++ show st

instance Show MonaGuideRule where
  show (MonaGuideRule name src dest) = name ++ ": " ++ show src ++ " -> " ++ "(" ++ show dest ++ ")"


lexer = makeTokenParser emptyDef
m_comma = lexeme lexer (char ',')
m_lparen = lexeme lexer (char '(')
m_rparen = lexeme lexer (char ')')
m_ddot = lexeme lexer (char ':')
m_to = lexeme lexer (string "->")
m_quot = lexeme lexer (char '\'')
m_statespace = lexeme lexer (string "State space")
m_size = lexeme lexer (string "size")
m_initial = lexeme lexer (string "Initial state:")
m_trans = lexeme lexer (string "Transitions:")
m_guide = lexeme lexer (string "Guide:")
m_gtaheader = lexeme lexer (string "GTA for formula with free variables:")
m_accept = lexeme lexer (string "Accepting states:")
m_reject = lexeme lexer (string "Rejecting states:")
m_white = whiteSpace lexer
m_space = lexeme lexer ((oneOf " "))
m_variable = many1 alphaNum


m_eol :: Parser String
m_eol = try (string "\n\r")
  <|> string "\r\n"
  <|> string "\n"
  <|> string "\r"
  <?> "end of line"


parseFile :: FilePath -> IO MonaGTA
parseFile filename = do
  str <- readFile filename
  return $ parseString str


parseString :: String -> MonaGTA
parseString str = case (parse parseGTA "MonaAutomataParser" str) of
  Left err   -> error $ show err
  Right res  -> res


parseTuple :: Parser String
parseTuple = lexeme lexer (many1 alphaNum)

number :: Parser String
number = many digit


guideName :: Parser String
guideName = lexeme lexer (many1 (noneOf " \t\n:()"))


parseTransition :: Parser MonaTransition
parseTransition = do
  m_white
  m_lparen
  s <- sepBy parseTuple m_comma
  m_rparen
  m_to
  dest <- parseTuple
  return $ makeTransition (init s) (last s) dest


parseGuideRule :: Parser MonaGuideRule
parseGuideRule = do
  m_white
  name <- guideName
  m_ddot
  src <- parseTuple
  m_to
  m_lparen
  dst <- sepBy parseTuple m_comma
  m_rparen
  return $ makeGuideRule name src dst


parseTransitionSet :: Parser [MonaTransition]
parseTransitionSet = do
  trans <- many (try parseTransition)
  return trans


parseGuideRuleSet :: Parser [MonaGuideRule]
parseGuideRuleSet = do
  gds <- many (try parseGuideRule)
  return gds


parseGuide :: Parser MonaGuide
parseGuide = do
  m_white
  m_guide
  rules <- parseGuideRuleSet
  return $ MonaGuide rules


parseStateSpaceHeader :: Parser MonaStateSpace
parseStateSpaceHeader = do
  m_white
  m_statespace
  iden <- parseTuple
  m_quot
  name <- guideName
  m_quot
  m_lparen
  m_size
  size <- parseTuple
  m_rparen
  m_ddot
  return $ MonaStateSpace (read iden :: Int) name (read size :: Int) 0 [] --Dangerous, default 0 is for Int, not for general MonaState


parseStateSpace :: Parser MonaStateSpace
parseStateSpace = do
  sp <- parseStateSpaceHeader
  m_initial
  ini <- parseTuple
  m_trans
  trans <- parseTransitionSet
  return $ MonaStateSpace {iden = iden sp, name=name sp, size=size sp,
    initial=(read ini :: Int), transitions=trans}


parseGTAHeader :: Parser MonaGTAHeader
parseGTAHeader = do
  m_white
  m_gtaheader
  vars <- sepBy m_variable m_space
  newline
  m_accept
  acc <- sepBy m_variable m_space
  newline
  m_reject
  reject <- sepBy m_variable m_space
  return $ MonaGTAHeader vars (toInt acc) (toInt reject)


parseGTA :: Parser MonaGTA
parseGTA = do
  guide <- parseGuide
  header <- parseGTAHeader
  return $ MonaGTA header guide []


toInt :: [String] -> [Int]
toInt = map (\a -> read a :: Int)


makeGuideRule :: String -> String -> [String] -> MonaGuideRule
makeGuideRule name src dest = MonaGuideRule name (read src :: Int) (toInt dest)


makeTransition :: [String] -> String -> String -> MonaTransition
makeTransition sts sym st = MonaTransition (toInt sts) sym (read st :: Int)
