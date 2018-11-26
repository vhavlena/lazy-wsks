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
-- Part with the Literal type
--------------------------------------------------------------------------------------------------------------

data Literal =
  Var Int
  | Not Literal
  deriving (Eq, Ord)

type SymTerm = (Set.Set Literal, Term)


--------------------------------------------------------------------------------------------------------------
-- Part with the Minus symbols symbolically (pre on the terms)
--------------------------------------------------------------------------------------------------------------

joinTerm :: Term -> Term -> Term
joinTerm (TSet t1) (TSet t2) = TSet $ Set.union t1 t2
joinTerm (TProj v1 t1) (TProj v2 t2) = TProj v1 (joinTerm t1 t2)
joinTerm _ _ = error "joinTerm: structure"


minusSymbolSym :: Term -> Term -> Set.Set Alp.Symbol -> [SymTerm]
minusSymbolSym t1@(TStates aut1 var1 st1) t2@(TStates aut2 var2 st2) sym =
  lst where
    lst = [(convSymToFle s, minusSymbol t1 t2 s) | s <- unsyms]
    unsyms = Set.toList $ Alp.unwindSymbolsX $ Alp.cylindrifySymbols var1 sym
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
minusSymbolSym (TProj v1 t1) (TProj v2 t2) sym
  | v1 /= v2 = error "minusSymbolSym: Projection variables do not match"
  | v1 == v2 = unifySymTerm $ map (g) l
    where
      l = minusSymbolSym t1 t2 (Alp.projSymbolsX sym v1)
      var = Aux.strToUniqInt v1
      g (f, t) = (Set.delete (Not $ Var var) (Set.delete (Var var) f), TProj v1 t)
minusSymbolSym (TSet tset1) (TSet tset2) sym = ret where
  cr = List.nub $ [minusSymbolSym t1 t2 sym | t1 <- Set.toList tset1, t2 <- Set.toList tset2]
  cr' = map (\(a,b) -> (a, [b])) $ foldr (++) [] cr
  ret = map (\(a,b) -> (a, TSet $ Set.fromList b)) $ Map.toList $ Map.fromListWith (++) cr'


unifySymTerm :: [SymTerm] -> [SymTerm]
unifySymTerm = Map.toList . Map.fromListWith (joinTerm)


forgetFle :: [SymTerm] -> [Term]
forgetFle = map (snd)


convSymToFle :: Alp.Symbol -> Set.Set Literal
convSymToFle (lst, var) = Set.fromList $ zipWith (fmerge) lst (List.sort $ Set.toList var)
  where
    fmerge sym var
      | sym == '0' = Not $ Var $ Aux.strToUniqInt var
      | sym == '1' = Var $ Aux.strToUniqInt var
      | otherwise = error $ "convSymToFle: unrecognized symbol"


getSatUnsat :: Set.Set Literal -> (Set.Set Int, Set.Set Int)
getSatUnsat s = (proj sat, proj $ s Set.\\ sat) where
  sat = Set.filter g s
  g (Var v) = True
  g _ = False
  proj = Set.map (fn)
  fn (Var v) = v
  fn (Not x) = fn x


isSatConjSet :: Set.Set Literal -> Set.Set Literal -> Bool
isSatConjSet s1 s2 = (Set.disjoint sat1 unsat2) && (Set.disjoint sat2 unsat1) where
  (sat1, unsat1) = getSatUnsat s1
  (sat2, unsat2) = getSatUnsat s2


satTermProductWith :: [SymTerm] -> [SymTerm] -> (Term -> Term -> Term) -> [SymTerm]
satTermProductWith l1 l2 cons = [(Set.union f1 f2, cons t1 t2) | (f1, t1) <- l1, (f2, t2) <- l2, isSatConjSet f1 f2]


--------------------------------------------------------------------------------------------------------------
-- Part with debug functions
--------------------------------------------------------------------------------------------------------------

test1 = minusSymbolSym t3 t4 (Set.singleton ("X", Set.fromList ["Y"]) ) where
  t1 = atom2Terms Map.empty (Lo.Subseteq "X" "Y")
  t2 = atom2Terms Map.empty (Lo.Subseteq "X" "Y")
  t3 = TProj "X" t1
  t4 = TProj "X" t2
