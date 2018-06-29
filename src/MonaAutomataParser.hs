{-|
Module      : MonaParser
Description : Mona formulae parser
Author      : Vojtech Havlena, June 2018
License     : GPL-3
-}

module MonaParser where

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

languageDef = error "Unimplemented"
