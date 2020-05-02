{-|
Module      : MonaParser
Description : Mona formulae parser
Author      : Ondrej Lengal, 2018
License     : GPL-3
-}

module MonaParser where

import Control.Applicative ((<*))

import Data.List

import MonaFormula
import AuxFunctions
import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token


parseFile :: FilePath -> IO (Either ParseError MonaFile)
parseFile filename = do
  str <- readFile filename
  return $ parseString str


parseString :: String -> Either ParseError MonaFile
parseString str = parse monaFileParser "" str
  -- case (parse monaFileParser "MONA parser" str) of
  -- Left err   -> error $ "hello: " ++ (show err)
  -- Right res  -> res
-- parseString = error "Unimplemented"


def = emptyDef{ commentStart = "/*"
              , commentEnd = "*/"
              , commentLine = "#"
              , nestedComments = False
              , caseSensitive = True
              , identStart = letter <|> char '_' <|> char '$' <|> char '\''
              , identLetter = alphaNum <|> char '_' <|> char '$' <|> char '\''
              , opStart = oneOf "~&:|.<=>+-,\"\\^"
              , opLetter = oneOf "~&:|.<=>+-,\"\\^"
              , reservedOpNames =
                [ "~"     -- NOT
                , "&"     -- AND
                , "|"     -- OR
                , "=>"    -- IMPLIES
                , "<=>"   -- EQUIV
                , "="     -- EQUALS
                , "~="    -- NEQUALS
                , "<"     -- LT
                , "<="    -- LEQ
                , ">"     -- GT
                , ">="    -- GEQ
                , "+"     -- PLUS
                , "-"     -- MINUS
                , ":"     --
                , ","     --
                , "."
                , "^"
                , "\\"
                --, ".1"    -- Right successor
                --, ".0"    -- Right successor
                ]
              , reservedNames =
                [ "ex0"
                , "ex1"
                , "ex2"
                , "all0"
                , "all1"
                , "all2"
                , "var0"
                , "var1"
                , "var2"
                , "let0"
                , "let1"
                , "let2"
                , "sub"
                , "in"
                , "notin"
                , "true"
                , "false"
                , "macro"
                , "pred"
                , "allpos"
                , "type"
                , "ws1s"
                , "ws2s"
                , "m2l-str"
                , "m2l-tree"
                , "where"
                , "export"
                , "import"
                , "restrict"
                , "empty"
                , "prefix"
                , "root"
                , "variant"
                , "type"
                , "in_state_space"
                , "tree"
                , "sometype"
                , "min"
                , "max"
                , "assert"
                , "pconst"
                , "union"
                , "inter"
                , "tree_root"
                , "succ"
                , "const_tree"
                , "universe"
                , "guide"
                , "include"
                , "execute"
                , "const"
                , "sing"
                , "cat1"
                , "..."
                , "lastpos"
                ]
              }


-- generate parsers
TokenParser{ parens = m_parens
           , braces = m_braces
           , identifier = m_identifier
           , reservedOp = m_reservedOp
           , reserved = m_reserved
           , comma = m_comma
           , commaSep = m_commaSep
           , commaSep1 = m_commaSep1
           , semi = m_semi
           , semiSep1 = m_semiSep1
           , natural = m_natural
           , stringLiteral = m_stringLiteral
           , whiteSpace = m_whiteSpace } = makeTokenParser def


-- parses terms
termParser :: Parser MonaTerm
termParser = buildExpressionParser termOpTable termP <?> "term"

-- term operator table
termOpTable = [ [ Infix (m_reservedOp "+" >> return MonaTermPlus) AssocLeft
                , Infix (m_reservedOp "." >> return MonaTermCat) AssocLeft
                , Postfix (m_reservedOp "^" >> return MonaTermUp)
                , Infix (m_reservedOp "-" >> return MonaTermMinus) AssocLeft
                , Infix (m_reservedOp "union" >> return MonaTermUnion) AssocLeft
                , Infix (m_reservedOp "inter" >> return MonaTermInter) AssocLeft
                , Infix (m_reservedOp "\\" >> return MonaTermDifference) AssocLeft
                ]
              ]

termP :: Parser MonaTerm
termP = m_parens termParser
    <|> try (do { t <- m_braces $ m_commaSep termParam
                ; return $ MonaTermSet t
              })
    <|> try (do { m_reserved "pconst"
                ; n <- m_parens $ m_natural
                ; return (MonaTermPConst n)
                })
    <|> fmap MonaTermVar m_identifier
    <|> fmap MonaTermConst m_natural
    <|>  (m_reserved "root" >> return MonaTermRoot)
    <|>  (m_reserved "empty" >> return MonaTermEmpty)
    <|>  (m_reserved "..." >> return MonaTermDots)


-- parses terms
termParamParser :: Parser MonaTerm
termParamParser = buildExpressionParser termOpTable termParam <?> "term"


termParam :: Parser MonaTerm
termParam = m_parens termParamParser
    <|> fmap MonaTermBool atomicFormulaParser
    <|> try (do { m_reserved "pconst"
                ; n <- m_parens $ m_natural
                ; return (MonaTermPConst n)
                })
    <|> try (do { predname <- m_identifier
                ; args <- m_parens $ m_commaSep termParam
                ; return (MonaTermBoolCall predname $ args)
                })
    <|> termParser
    -- <|> fmap MonaTermVar m_identifier
    -- <|> fmap MonaTermConst m_natural
    -- <|> (m_reserved "root" >> return MonaTermRoot)


-- sanitizes terms
sanitizeTerm :: MonaTerm -> MonaTerm
sanitizeTerm = error "Unimplemented"


-- parses a binary atom
binAtomParser :: String -> (MonaTerm -> MonaTerm -> MonaAtom) -> Parser MonaAtom
binAtomParser op f = do { lhs <- termParser
                      ; m_reservedOp op
                      ; rhs <- termParser
                      ; return (f lhs rhs) ---((show lhs) ++ " " ++ op ++ " " ++ (show rhs)))
                      }


-- binAtomParserSuff :: String -> String -> Parser MonaFormula
-- binAtomParserSuff op suff = do { lhs <- termParser
--                                ; m_reservedOp op
--                                ; rhs <- termParser
--                                ; m_reservedOp suff
--                                ; return (MonaFormulaAtomic ((show lhs) ++ " " ++ op ++ suff ++ " " ++ (show rhs)))
--                              }


-- parses atomic formulae
atomicFormulaParser :: Parser MonaAtom
atomicFormulaParser = try (binAtomParser "=" (MonaAtomEq))
                  <|> try (binAtomParser "~=" (MonaAtomNeq))
                  <|> try (binAtomParser "<" (MonaAtomLe))
                  <|> try (binAtomParser "<=" (MonaAtomLeq))
                  <|> try (binAtomParser ">" (MonaAtomGe))
                  <|> try (binAtomParser ">=" (MonaAtomGeq))
                  <|> try (binAtomParser "in" (MonaAtomIn))
                  <|> try (binAtomParser "notin" (MonaAtomNotIn))
                  <|> try (binAtomParser "sub" (MonaAtomSub))
                  <?> "atomic formula"


-- parses a "varwhere" string
varWhereParser :: Parser (String, Maybe MonaFormula)
varWhereParser = do { varname <- m_identifier
                    ; phi <- optionMaybe (m_reserved "where" >> formulaParser)
                    ; return (varname, phi)
                    }

-- parses formulae
formulaParser :: Parser MonaFormula
formulaParser = buildExpressionParser formulaOpTable formulaTerm <?> "formula"

-- formula operator table
formulaOpTable = [ [ Prefix (m_reservedOp "~"   >> return MonaFormulaNeg) ]
                 , [ Infix  (m_reservedOp "&"   >> return MonaFormulaConj) AssocLeft ]
                 , [ Infix  (m_reservedOp "|"   >> return MonaFormulaDisj) AssocLeft ]
                 , [ Infix  (m_reservedOp "=>"  >> return MonaFormulaImpl) AssocRight ]
                 , [ Infix  (m_reservedOp "<=>" >> return MonaFormulaEquiv) AssocRight ]
                 ]

formulaTerm :: Parser MonaFormula
formulaTerm = m_parens formulaParser
          <|> do { atom <- atomicFormulaParser
                 ; return $ MonaFormulaAtomic atom
                 }
          <|> (m_reserved "true" >> return (MonaFormulaAtomic $ MonaAtomTrue))
          <|> (m_reserved "false" >> return (MonaFormulaAtomic $ MonaAtomFalse))
          <|> do { m_reserved "sing"
                 ; var <- m_identifier
                 ; return (MonaFormulaAtomic $ MonaAtomSing $ MonaTermVar var )
                 }
          <|> do { m_reserved "empty"
                 ; term <- termParser
                 ; return (MonaFormulaAtomic $ MonaAtomIsEmpty term )
                 }
          <|> do { m_reserved "eps"
                ; var <- m_identifier
                ; return (MonaFormulaAtomic $ MonaAtomEps $ MonaTermVar var )
                }
          <|> do { m_reserved "ex0"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; let varList = map fst varWhereList
                 ; return (MonaFormulaEx0 varList phi)
                 }
          <|> do { m_reserved "ex1"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaEx1 varWhereList phi)
                 }
          <|> do { m_reserved "ex2"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaEx2 varWhereList phi)
                 }
          <|> do { m_reserved "all0"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; let varList = map fst varWhereList
                 ; return (MonaFormulaAll0 varList phi)
                 }
          <|> do { m_reserved "all1"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaAll1 varWhereList phi)
                 }
          <|> do { m_reserved "all2"
                 ; (varWhereList, phi) <- parseQuantSuffix
                 ; return (MonaFormulaAll2 varWhereList phi)
                 }
          <|> try (do { predname <- m_identifier
                      ; args <- m_parens $ m_commaSep termParam
                      ; return (MonaFormulaPredCall predname $ args)
                      })
          <|> fmap MonaFormulaVar m_identifier
  where
    parseQuantSuffix :: Parser ([(String, Maybe MonaFormula)], MonaFormula)
    parseQuantSuffix = do { varWhereList <- m_commaSep1 varWhereParser
                          ; m_reservedOp ":"
                          ; phi <- formulaParser
                          ; return (varWhereList, phi)
                          }

-- parses a MONA declaration
declarationParser :: Parser MonaDeclaration
declarationParser = do { m_reserved "var0"
                       ; varList <- m_commaSep1 m_identifier
                       ; return (MonaDeclVar0 varList)
                       }
                <|> do { m_reserved "var1"
                       ; varWhereList <- m_commaSep1 varWhereParser
                       ; return (MonaDeclVar1 varWhereList)
                       }
                <|> do { m_reserved "var2"
                       ; varWhereList <- m_commaSep1 varWhereParser
                       ; return (MonaDeclVar2 varWhereList)
                       }
                <|> do { m_reserved "allpos"
                       ; varname <- m_identifier
                       ; return (MonaDeclAllpos varname)
                       }
                <|> do { m_reserved "lastpos"
                       ; varname <- m_identifier
                       ; return (MonaDeclLastpos varname)
                       }
                <|> do { m_reserved "defaultwhere1"
                       ; varname <- m_parens m_identifier
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclDefWhere1 varname phi)
                       }
                <|> do { m_reserved "defaultwhere2"
                       ; varname <- m_parens m_identifier
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclDefWhere2 varname phi)
                       }
                <|> do { m_reserved "assert"
                       ; phi <- formulaParser
                       ; return (MonaDeclAssert phi)
                       }
                <|> do { m_reserved "const"
                       ; atom <- atomicFormulaParser
                       ; return (MonaDeclConst atom)
                       }
                <|> do { m_reserved "macro"
                       ; name <- m_identifier
                       ; args <- optionMaybe (m_parens $ m_commaSep paramParser)
                       ; let sanArgs = (case args of
                                          Nothing -> []
                                          Just ls -> ls
                                       )
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclMacro name sanArgs phi)
                       }
                <|> do { m_reserved "pred"
                       ; name <- m_identifier
                       ; args <- optionMaybe (m_parens $ m_commaSep paramParser)
                       ; let sanArgs = (case args of
                                          Nothing -> []
                                          Just ls -> ls
                                       )
                       ; m_reservedOp "="
                       ; phi <- formulaParser
                       ; return (MonaDeclPred name sanArgs phi)
                       }
                <|> do { m_reserved "export"
                       ; (filename, phi) <- m_parens
                           (do { fn <- m_stringLiteral
                               ; m_comma
                               ; phi' <- formulaParser
                               ; return (fn, phi')
                               }
                           )
                       ; return (MonaDeclExport filename phi)
                       }
                <|> fmap MonaDeclFormula formulaParser
                <?> "declaration"


-- parses macro/pred parameters
paramParser :: Parser MonaMacroParam
paramParser = do { m_reserved "var0"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar0 $ map fst varWhereList)
                 }
          <|> do { m_reserved "var1"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar1 varWhereList)
                 }
          <|> do { m_reserved "var2"
                 ; varWhereList <- parseParamNames
                 ; return (MonaMacroParamVar2 varWhereList)
                 }
          <?> "parameter"
  where
    parseParamNames :: Parser [(String, Maybe MonaFormula)]
    parseParamNames = sepBy1 varWhereParser (try parseComma)
    parseComma :: Parser ()
    parseComma = do { m_comma
                    ; notFollowedBy (m_reserved "var0" <|> m_reserved "var1" <|> m_reserved "var2")
                    }


-- parses a MONA file header
headerParser :: Parser String
headerParser = (m_reserved "ws1s" >> return "ws1s")
           <|> (m_reserved "ws2s" >> return "ws2s")
           <|> (m_reserved "m2l-str" >> return "m2l-str")
           <|> (m_reserved "m2l-tree" >> return "m2l-tree")


-- parses a MONA file
monaFileParser :: Parser MonaFile
monaFileParser = do { m_whiteSpace
                    ; domain <- optionMaybe (do { hdr <- headerParser
                                                ; m_semi
                                                ; return hdr
                                             })
                    ; decls <- many1 (declarationParser <* m_semi)
                    ; return MonaFile{mf_domain = domain, mf_decls = decls}
                    }
              <* eof
