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
import qualified ComTreeAutomaton as CTA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import BasicAutomata

import qualified Debug.Trace as Dbg


type MonaAutDict = Map.Map String WS2STreeAut
type WS2SComTA = CTA.ComTA State Alp.Symbol
type WS2SComState = CTA.ComState State


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
   | TTrue
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
showTermDbg ind (TTrue) = (replicate ind ' ') ++ "True"

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
   | aut1 == aut2 && var1 == var2 = TStates aut1 var1 (CTA.preCom (Alp.cylindrifySymbol) aut1 [st1, st2] sym)
   | otherwise = error "minusSymbol: Inconsistent basic automata"
minusSymbol t _ _ = error $ "minusSymbol: Minus symbol is defined only on term-pairs: " ++ show t


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives Set (a union b union ...).
unionTerms :: [Term] -> Set.Set Term
unionTerms [] = Set.empty
unionTerms ((TSet a):xs) = Set.union a (unionTerms xs)
unionTerms (t:xs) = Set.union (Set.singleton t) (unionTerms xs)


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives TSet (a union b union ...).
unionTSets :: [Term] -> Term
unionTSets = TSet . unionTerms


--------------------------------------------------------------------------------------------------------------
-- Part with the functions concerning compound states
--------------------------------------------------------------------------------------------------------------

flattenStates :: [Term] -> Term
flattenStates terms = foldr1 (fun) terms where
    fun (TStates aut1 var1 st1) (TStates aut2 var2 st2)
      | (aut1 == aut2) && (var1 == var2) = TStates aut1 var1 (unionComStates (Set.toList st1) (Set.toList st2))
      | otherwise = error "flattenStates: incompatible states"
    fun _ _ = error "flattenStates: incompatible states"


unionComStates :: [WS2SComState] -> [WS2SComState] -> Set.Set WS2SComState
unionComStates [CTA.SetSt st1] [CTA.SetSt st2] = Set.singleton $ CTA.SetSt $ Set.union st1 st2
unionComStates t1 t2 = Set.union (Set.fromList t1) (Set.fromList t2)


flattenList :: [Term] -> Maybe [Term]
flattenList lst =
  if null fil then Nothing
  else Just [flattenStates fil] where
    fil = filter (fun) lst
    fun (TStates _ _ _) = True
    fun _ = False


removeSet :: Term -> Term
removeSet (TSet set) =
  case flattenList lst of
    Just r -> TSet $ Set.fromList r
    Nothing -> TSet $ Set.fromList [removeSet t | t <- lst]
  where
    lst = Set.toList $ unionTerms $ Set.toList set
removeSet (TIntersect t1 t2) = TIntersect (removeSet t1) (removeSet t2)
removeSet (TUnion t1 t2) = TUnion (removeSet t1) (removeSet t2)
removeSet (TCompl t) = TCompl $ removeSet t
removeSet (TProj v1 t1) = TProj v1 (removeSet t1)
removeSet t = t


isSubsetStates [CTA.SetSt st1] [CTA.SetSt st2] = Just $ Set.isSubsetOf st1 st2
isSubsetStates _ _ = Nothing


subsetSetStates :: Set.Set WS2SComState -> Set.Set WS2SComState -> Bool
subsetSetStates s1 s2 =
  case isSubsetStates lst1 lst2 of
    Just a -> a
    Nothing -> Set.isSubsetOf s1 s2
  where
    lst1 = Set.toList s1
    lst2 = Set.toList s2


--------------------------------------------------------------------------------------------------------------
-- Part with the functions providing conversions from a formuala to terms.
--------------------------------------------------------------------------------------------------------------

-- |Convert atomic formula to term.
atom2Terms :: MonaAutDict -> Lo.Atom -> Term
atom2Terms _ (Lo.Sing var) = constructTermAtom (singAut var) [var]
atom2Terms _ (Lo.Cat1 v1 v2) = constructTermAtom (cat1Aut v1 v2) [v1, v2]
atom2Terms _ (Lo.Cat2 v1 v2) = constructTermAtom (cat2Aut v1 v2) [v1, v2]
atom2Terms _ (Lo.Subseteq v1 v2) = constructTermAtom (subseteqAut v1 v2) [v1, v2]
atom2Terms _ (Lo.Eps var) = constructTermAtom (epsAut var) [var]
atom2Terms _ (Lo.Eqn v1 v2) = constructTermAtom (eqAut v1 v2) [v1, v2]
atom2Terms _ (Lo.In v1 v2) = constructTermAtom (inAut v1 v2) [v1, v2]
atom2Terms _ (Lo.Subset v1 v2) = constructTermAtom (subsetAut v1 v2) [v1, v2]
atom2Terms _ (Lo.Neq v1 v2) = TCompl $ constructTermAtom (eqAut v1 v2) [v1, v2]
atom2Terms _ (Lo.AtTrue) = TTrue
atom2Terms autdict (Lo.MonaAt at vars) = case (Map.lookup (show at) autdict) of
  Just aut -> TStates (CTA.Base aut vars) vars (Set.singleton $ CTA.SetSt (TA.leaves aut))
  Nothing -> error "Internal error: cannot find corresponding mona automaton"


constructTermAtom :: WS2STreeAut -> [Alp.Variable] -> Term
constructTermAtom aut vars = TStates (CTA.Base aut vars) vars (Set.singleton $ CTA.SetSt (TA.leaves aut))


joinSetTerm :: Term -> Term
joinSetTerm (TSet s) = TSet $ Set.map (joinSetTerm) s
joinSetTerm (TUnion t1 t2) = joinStatesTerm $ TUnion (joinSetTerm t1) (joinSetTerm t2)
joinSetTerm (TIntersect t1 t2) = joinStatesTerm $ TIntersect (joinSetTerm t1) (joinSetTerm t2)
joinSetTerm (TCompl t1) = TCompl $ joinSetTerm t1
joinSetTerm (TProj var t) = TProj var (joinSetTerm t)
joinSetTerm (TMinusClosure t sym) = TMinusClosure (joinSetTerm t) sym
joinSetTerm t = t


joinStatesTerm :: Term -> Term
joinStatesTerm (TIntersect (TStates aut1 vars1 st1) (TStates aut2 vars2 st2)) =
    TStates (CTA.ConjTA aut1 aut2) (List.nub $ vars1 ++ vars2) (expand (CTA.ConjSt) st1 st2)
joinStatesTerm (TUnion (TStates aut1 vars1 st1) (TStates aut2 vars2 st2)) =
    TStates (CTA.DisjTA aut1 aut2) (List.nub $ vars1 ++ vars2) (expand (CTA.DisjSt) st1 st2)
joinStatesTerm t = t


expand :: (WS2SComState -> WS2SComState -> WS2SComState) -> Set.Set WS2SComState
  -> Set.Set WS2SComState -> Set.Set WS2SComState
expand f s1 s2 = Set.fromList $ [f a b | a <- unwindFromSet $ Set.toList s1, b <- unwindFromSet $ Set.toList s2]


unwindFromSet :: [WS2SComState] -> [WS2SComState]
unwindFromSet [CTA.SetSt st] = map (CTA.State) (Set.toList st)
unwindFromSet t = t


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
