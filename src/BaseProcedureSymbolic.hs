{-|
Module      : BaseProcedureSymbolic
Description : Auxiliary functions for symbolic handling with symbols and
              transition relation (BDD based approach) in WS2S decision
              procedure.
Author      : Vojtech Havlena, November 2018
License     : GPL-3
-}

module BaseProcedureSymbolic where

import Data.Maybe
import Data.Boolean.SatSolver
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified ComTreeAutomaton as CTA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import BaseDecisionProcedure

import qualified Debug.Trace as Dbg

--------------------------------------------------------------------------------------------------------------
-- Part with the Minus symbols symbolically (pre on the terms)
--------------------------------------------------------------------------------------------------------------

type SymTerm = (Boolean, Term)

instance Eq Boolean where
  Var v1 == Var v2 = v1 == v2
  (f1 :&&: f2) == (f3 :&&: f4) = (f1 == f3) && (f2 == f4)
  (f1 :||: f2) == (f3 :||: f4) = (f1 == f3) && (f2 == f4)
  Not f1 == Not f2 = f1 == f2
  _ == _ = False


minusSymbolSym :: Term -> Term -> Set.Set Alp.Symbol -> [SymTerm]
minusSymbolSym (TStates aut1 var1 st1) (TStates aut2 var2 st2) sym = error "Unimplemented"
minusSymbolSym (TIntersect t1 t2) (TIntersect t3 t4) sym = List.nub $ satTermProductWith l1 l2 (TIntersect)
  where
    l1 = minusSymbolSym t1 t3 sym
    l2 = minusSymbolSym t2 t4 sym
minusSymbolSym (TUnion t1 t2) (TUnion t3 t4) sym = satTermProductWith l1 l2 (TUnion)
  where
    l1 = minusSymbolSym t1 t3 sym
    l2 = minusSymbolSym t2 t4 sym
minusSymbolSym (TCompl t1) (TCompl t2) sym = map g (minusSymbolSym t1 t2 sym)
  where
    g (a,b) = (a, TCompl b)


convSymToFle :: Alp.Symbol -> Boolean
convSymToFle (lst, var) = foldr (:&&:) Yes $ zipWith (fmerge) lst (List.sort $ Set.toList var)
  where
    fmerge sym var
      | sym == '0' = Not $ Var $ Aux.strToUniqInt var
      | sym == '1' = Var $ Aux.strToUniqInt var
      | otherwise = error $ "convSymToFle: unrecognized symbol"


satTermProductWith :: [SymTerm] -> [SymTerm] -> (Term -> Term -> Term) -> [SymTerm]
satTermProductWith l1 l2 cons = [(f1 :&&: f2, cons t1 t2) | (f1, t1) <- l1, (f2, t2) <- l2, isSat f1 f2]
  where
    isSat f1 f2 = isJust $ ((assertTrue f1 newSatSolver >>= assertTrue f2 >>= return . isSolvable) :: Maybe Bool)
