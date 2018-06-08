{-|
Module      : Alphabet
Description : Functions for working with symbols with variables.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module Alphabet (
   Variable
   , Symbol
   , emptySymbol
   , projSymbol
   , projSymbolVars
   , remSymbol
   , remSymbolVars
   , cylindrifySymbol
   , cylindrifySymbols
   , showSymbolDbg
) where


import qualified Data.Set as Set
import qualified Data.List as List
import qualified AuxFunctions as Aux


type Variable = String
type Symbol = ([Char], Set.Set Variable)


-- |Empty symbol = epsilon
emptySymbol = ([], Set.empty)


-- |Show symbol in human readable debug format.
showSymbolDbg :: Symbol -> String
showSymbolDbg (str, _) = str


-- |Make projection of a symbol wrt a given variable (i.e. it returns symbols
-- where the values of this variable are set to 0, 1).
projSymbol :: Symbol -> Variable -> Set.Set Symbol
projSymbol (lst, vars) new =
   case List.elemIndex new (List.sort $ Set.toList vars') of
      Just idx -> Set.fromList [(Aux.insertAt a lst idx, vars') | a <- ['0','1']]
      Nothing -> error "projSymbol: Index not found"
   where
      vars' = Set.insert new vars


-- |Pointwise extension of projSymbol to a set of variables and a set of symbols.
projSymbolVars :: Set.Set Symbol -> [Variable] -> Set.Set Symbol
projSymbolVars s [] = s
projSymbolVars s (x:xs) = projSymbolVars s' xs where
   s' = foldr (Set.union) Set.empty [ projSymbol sym x | sym <- Set.toList s ]


-- |Remove value of given variable from a symbol.
remSymbol :: Symbol -> Variable -> Symbol
remSymbol (lst, vars) new =
   case List.elemIndex new (List.sort $ Set.toList vars) of
      Just idx -> (Aux.deleteAt lst idx, vars')
      Nothing -> error "remSymbol: Index not found"
   where
      vars' = Set.delete new vars


-- |Pointwise extension of remSymbol to a set of variables.
remSymbolVars :: Symbol -> [Variable] -> Symbol
remSymbolVars s [] = s
remSymbolVars s (x:xs) = remSymbolVars (remSymbol s x) xs


-- |Cylindrify symbol -- maintain values of only those variables which are in the list.
cylindrifySymbol :: [Variable] -> Symbol -> Symbol
cylindrifySymbol vars sym = remSymbolVars sym (Set.toList $ Set.difference (snd sym) (Set.fromList vars))

cylindrifySymbols :: [Variable] -> Set.Set Symbol -> Set.Set Symbol
cylindrifySymbols vars sym = Set.map (cylindrifySymbol vars) sym
