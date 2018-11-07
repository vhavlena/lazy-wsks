{-|
Module      : BaseDecisionProcedure
Description : Auxiliary functions for WS2S decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module BaseDecisionProcedure where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import BasicAutomata

import qualified Debug.Trace as Dbg


type MonaAutDict = Map.Map String WS2STreeAut
type WS2SComTA = TA.ComTA State Alp.Symbol
type WS2SComState = TA.ComState State


-- |WS2S Lazy terms.
data Term =
   TStates WS2SComTA [Alp.Variable] (Set.Set WS2SComState)
   | TUnion Term Term
   | TIntersect Term Term
   | TCompl Term
   | TProj Alp.Variable Term
   | TMinusClosure Term (Set.Set Alp.Symbol)
   | TIncrSet Term Term
   | TPair Term Term
   | TSet (Set.Set Term)
   deriving (Eq, Ord)

sinkTerm = TSet $ Set.empty

--------------------------------------------------------------------------------------------------------------
-- Part with the term to string conversion.
--------------------------------------------------------------------------------------------------------------

instance Show Term where
   show = showTermDbg 0


-- |Prints the term in human readable format.
showTerm :: Term -> String
showTerm (TSet set) = "{" ++ show set ++ "}"
showTerm (TPair t1 t2) = "\n(\n\t" ++ showTerm t1 ++ "\n\t,\n\t" ++ showTerm t2 ++ "\n)\n"
showTerm (TMinusClosure t sym) = "(" ++ showTerm t ++ ") - {" ++ show sym ++ "}*"
showTerm (TProj var t) = "Proj_"++ show var ++ "( " ++ showTerm t ++ " )"
showTerm (TCompl t) = "¬(" ++ showTerm t ++ ")"
showTerm (TUnion t1 t2) = "(" ++ showTerm t1 ++ ") ∨ (" ++ showTerm t2 ++ ")"
showTerm (TIntersect t1 t2) = "(" ++ showTerm t1 ++ ") ∧ (" ++ showTerm t2 ++ ")"
showTerm (TStates _ _ st) = show st


-- |Prints the term in human readable debug format.
showTermDbg :: Int -> Term -> String
showTermDbg ind (TSet set) = "\n" ++ (replicate ind ' ') ++ "{" ++ unwords (map (\a -> "\n" ++ (replicate (ind+2) ' ') ++ (showTermDbg (ind+2) a) ++ ",") (Set.toList set)) ++ "\n" ++ (replicate ind ' ') ++ "}"
showTermDbg ind (TPair t1 t2) = "\n" ++ (replicate ind ' ') ++ "(\n" ++ showTermDbg (ind+2) t1 ++ "\n\t,\n\t" ++ showTermDbg (ind+2) t2 ++ "\n)\n"
showTermDbg ind (TMinusClosure t sym) = "(" ++ showTermDbg ind t ++ (replicate ind ' ') ++ ") - {" ++ show (map (Alp.showSymbolDbg) (Set.toList sym)) ++ "}*"
showTermDbg ind (TProj var t) = "Proj_"++ show var ++ "( " ++ showTermDbg ind t ++ " )"
showTermDbg ind (TCompl t) = "¬(" ++ showTermDbg ind t ++ ")"
showTermDbg ind (TUnion t1 t2) = "(" ++ showTermDbg ind t1 ++ ") ∨ (" ++ showTermDbg ind t2 ++ ")"
showTermDbg ind (TIntersect t1 t2) = "(" ++ showTermDbg ind t1 ++ ") ∧ (" ++ showTermDbg ind t2 ++ ")"
showTermDbg ind (TStates _ _ st) = (show $ Set.toList st)
showTermDbg ind (TIncrSet a b) = (showTermDbg ind a)  ++ "---" ++ (showTermDbg ind b)

--------------------------------------------------------------------------------------------------------------
-- Part with the Minus symbol (pre on the terms)
--------------------------------------------------------------------------------------------------------------

-- |Term minus symbol -- defined only for the term-pairs.
minusSymbol :: Term -> Term -> Alp.Symbol -> Term
minusSymbol t1 (TSet t2) sym
   | t2 == Set.empty = sinkTerm
minusSymbol (TSet t1) t2 sym
   | t1 == Set.empty = sinkTerm
minusSymbol (TIntersect t1 t2) (TIntersect t3 t4) sym = TIntersect (minusSymbol t1 t3 sym) (minusSymbol t2 t4 sym)
minusSymbol (TUnion t1 t2) (TUnion t3 t4) sym = TUnion (minusSymbol t1 t3 sym) (minusSymbol t2 t4 sym)
minusSymbol (TCompl t1) (TCompl t2) sym = TCompl (minusSymbol t1 t2 sym)
minusSymbol (TProj v1 t1) (TProj v2 t2) sym
   | v1 == v2 = TProj v1 (TSet $ unionTerms [minusSymbol t1 t2 s | s <- Set.toList $ Alp.projSymbol sym v1])
   | otherwise = error "minusSymbol: Projection variables do not match"
minusSymbol (TSet tset1) (TSet tset2) sym = TSet (Set.fromList [minusSymbol t1 t2 sym | t1 <- Set.toList tset1, t2 <- Set.toList tset2])
minusSymbol (TStates aut1 var1 st1) (TStates aut2  var2 st2) sym
   | aut1 == aut2 && var1 == var2 = TStates aut1 var1 (TA.pre aut1 [st1, st2] (Alp.cylindrifySymbol var1 sym))
   | otherwise = error "minusSymbol: Inconsistent basic automata"
--minusSymbol (TMinusClosure t1 _) (TMinusClosure t2 _) sym = minusSymbol t1 t2 sym
--minusSymbol (TMinusClosure t1 _) term2@(TSet t2) sym = minusSymbol t1 term2 sym
--minusSymbol term2@(TSet t2) (TMinusClosure t1 _) sym = minusSymbol t1 term2 sym
minusSymbol t _ _ = error $ "minusSymbol: Minus symbol is defined only on term-pairs: " ++ show t


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives Set (a union b union ...).
unionTerms :: [Term] -> Set.Set Term
unionTerms [] = Set.empty
unionTerms ((TSet a):xs) = Set.union a (unionTerms xs)


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives TSet (a union b union ...).
unionTSets :: [Term] -> Term
unionTSets = TSet . unionTerms


--------------------------------------------------------------------------------------------------------------
-- Part with the functions providing conversions from a formuala to terms.
--------------------------------------------------------------------------------------------------------------

-- |Convert atomic formula to term.
atom2Terms :: MonaAutDict -> Lo.Atom -> Term
atom2Terms _ (Lo.Sing var) = TStates (TA.Base aut) [var] (Set.map (TA.State) (TA.leaves aut)) where
   aut = singAut var
atom2Terms _ (Lo.Cat1 v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = cat1Aut v1 v2
atom2Terms _ (Lo.Cat2 v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = cat2Aut v1 v2
atom2Terms _ (Lo.Subseteq v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = subseteqAut v1 v2
atom2Terms _ (Lo.Eps var) = TStates (TA.Base aut) [var] (Set.map (TA.State) (TA.leaves aut)) where
   aut = epsAut var
atom2Terms _ (Lo.Eqn v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = eqAut v1 v2
atom2Terms _ (Lo.In v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = inAut v1 v2
atom2Terms _ (Lo.Subset v1 v2) = TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = subsetAut v1 v2
atom2Terms _ (Lo.Neq v1 v2) = TCompl $ TStates (TA.Base aut) [v1, v2] (Set.map (TA.State) (TA.leaves aut)) where
   aut = eqAut v1 v2
atom2Terms autdict (Lo.MonaAtom iden vars) = case (Map.lookup iden autdict) of
  Just aut -> TStates aut vars (TA.leaves aut)
  Nothing -> error "Internal error: cannot find corresponding mona automaton"


joinSetTerm :: Term -> Term
--joinSetTerm (TUnion (TSet s1) (TSet s2)) = TSet $ Set.fromList [ TUnion t1 t2 | t1 <- Set.toList s1, t2 <- Set.toList s2 ]
--joinSetTerm (TIntersect (TSet s1) (TSet s2)) = TSet $ Set.fromList [ TIntersect t1 t2 | t1 <- Set.toList s1, t2 <- Set.toList s2 ]
joinSetTerm (TSet s) = TSet $ Set.map (joinSetTerm) s
joinSetTerm (TUnion t1 t2) = joinStatesTerm $ TUnion (joinSetTerm t1) (joinSetTerm t2)
joinSetTerm (TIntersect t1 t2) = joinStatesTerm $ TIntersect (joinSetTerm t1) (joinSetTerm t2)
joinSetTerm (TCompl t1) = TCompl $ joinSetTerm t1
joinSetTerm (TProj var t) = TProj var (joinSetTerm t)
joinSetTerm (TMinusClosure t sym) = TMinusClosure (joinSetTerm t) sym
--joinSetTerm (TStates aut var st)
joinSetTerm t = t


joinStatesTerm :: Term -> Term
joinStatesTerm (TIntersect (TStates aut1 vars1 st1) (TStates aut2 vars2 st2)) =
    TStates (TA.ConjTA aut1 aut2) (nub $ vars1 ++ vars2) (expand (TA.ConjSt) st1 st2)
joinStatesTerm (TUnion (TStates aut1 vars1 st1) (TStates aut2 vars2 st2)) =
    TStates (TA.DisjTA aut1 aut2) (nub $ vars1 ++ vars2) (expand (TA.DisjSt) st1 st2)
joinStatesTerm t = t


-- |Convert formula to term representation. Uses additional information about
-- quantified variables reachable to a given term.
formula2TermsVars :: MonaAutDict -> Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVars autdict (Lo.FormulaAtomic atom) vars = atom2Terms autdict atom
formula2TermsVars autdict (Lo.Disj f1 f2) vars = TUnion (formula2TermsVars autdict f1 vars) (formula2TermsVars autdict f2 vars)
formula2TermsVars autdict (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVars autdict f1 vars) (formula2TermsVars autdict f2 vars)
formula2TermsVars autdict (Lo.Neg f) vars = TCompl (formula2TermsVars autdict f vars)
formula2TermsVars autdict (Lo.Exists var f) vars =
   TProj var (TMinusClosure (TSet (Set.fromList [formula2TermsVars autdict f (var:vars)])) (Alp.projZeroSymbol (var:vars)))
formula2TermsVars _ (Lo.ForAll _ _) _ = error "formula2TermsVars: Only formulas without forall are allowed"
