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


-- |WS2S Lazy terms.
data Term =
   TStates WS2STreeAut [Alp.Variable] (Set.Set State)
   | TUnion Term Term
   | TIntersect Term Term
   | TCompl Term
   | TProj Alp.Variable Term
   | TMinusClosure Term (Set.Set Alp.Symbol)
   | TIncrSet Term Term
   | TPair Term Term
   | TSet (Set.Set Term)
   deriving (Eq, Ord)

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


-- |Term minus symbol -- defined only for the term-pairs.
minusSymbol :: Term -> Alp.Symbol -> Term
minusSymbol (TPair (TIntersect t1 t2) (TIntersect t3 t4)) sym = TIntersect (minusSymbol (TPair t1 t3) sym) (minusSymbol (TPair t2 t4) sym)
minusSymbol (TPair (TUnion t1 t2) (TUnion t3 t4)) sym = TUnion (minusSymbol (TPair t1 t3) sym) (minusSymbol (TPair t2 t4) sym)
minusSymbol (TPair (TCompl t1) (TCompl t2)) sym = TCompl (minusSymbol (TPair t1 t2) sym)
minusSymbol (TPair (TProj v1 t1) (TProj v2 t2)) sym
   | v1 == v2 = TProj v1 (TSet $ unionTerms [minusSymbol (TPair t1 t2) s | s <- Set.toList $ Alp.projSymbol sym v1])
   | otherwise = error "minusSymbol: Projection variables do not match"
minusSymbol (TPair (TSet tset1) (TSet tset2)) sym = TSet (Set.fromList [minusSymbol (TPair t1 t2) sym | t1 <- Set.toList tset1, t2 <- Set.toList tset2])
minusSymbol (TPair (TStates aut1 var1 st1) (TStates aut2  var2 st2)) sym
   | aut1 == aut2 && var1 == var2 = TStates aut1 var1 (TA.pre aut1 [st1, st2] (Alp.cylidrifySymbol sym var1))
   | otherwise = error "minusSymbol: Inconsistent basic automata"
minusSymbol (TPair term1@(TMinusClosure t1 _) term2@(TMinusClosure t2 _)) sym = minusSymbol (TPair t1 t2) sym
minusSymbol (TPair (TMinusClosure t1 _) term2@(TSet t2)) sym = minusSymbol (TPair t1 term2) sym
minusSymbol (TPair term2@(TSet t2) (TMinusClosure t1 _)) sym = minusSymbol (TPair t1 term2) sym
minusSymbol (TPair (TIncrSet a _) b) sym = minusSymbol (TPair a b) sym
minusSymbol (TPair a (TIncrSet b _)) sym = minusSymbol (TPair a b) sym
minusSymbol t _ = error $ "minusSymbol: Minus symbol is defined only on term-pairs: " ++ show t


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives Set (a union b union ...).
unionTerms :: [Term] -> Set.Set Term
unionTerms [] = Set.empty
unionTerms ((TSet a):xs) = Set.union a (unionTerms xs)
unionTerms ((TIncrSet a _):xs) = unionTerms (a:xs)


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives TSet (a union b union ...).
unionTSets :: [Term] -> Term
unionTSets = TSet . unionTerms


-- |Convert atomic formula to term.
atom2Terms :: Lo.Atom -> Term
atom2Terms (Lo.Sing var) = TStates aut [var] (TA.leaves aut) where
   aut = singAut var
atom2Terms (Lo.Cat1 v1 v2) = TStates aut [v1, v2] (TA.leaves aut) where
   aut = catAut v1 v2
atom2Terms (Lo.Subseteq v1 v2) = TStates aut [v1, v2] (TA.leaves aut) where
   aut = subseteqAut v1 v2
atom2Terms (Lo.Eps var) = TStates aut [var] (TA.leaves aut) where
   aut = epsAut var
atom2Terms (Lo.Eqn v1 v2) = TStates aut [v1, v2] (TA.leaves aut) where
   aut = eqAut v1 v2


-- |Convert formula to term representation. Uses additional information about
-- quantified variables reachable to a given term.
formula2TermsVars :: Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVars (Lo.FormulaAtomic atom) vars = atom2Terms atom
formula2TermsVars (Lo.Disj f1 f2) vars = TUnion (formula2TermsVars f1 vars) (formula2TermsVars f2 vars)
formula2TermsVars (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVars f1 vars) (formula2TermsVars f2 vars)
formula2TermsVars (Lo.Neg f) vars = TCompl (formula2TermsVars f vars)
formula2TermsVars (Lo.Exists var f) vars =
   TProj var (TMinusClosure (TSet (Set.fromList [formula2TermsVars f (var:vars)])) (Alp.projSymbolVars (Set.fromList [Alp.emptySymbol]) (var:vars)))
formula2TermsVars (Lo.ForAll _ _) _ = error "formula2TermsVars: Only formulas without forall are allowed"
