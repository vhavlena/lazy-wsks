{-|
Module      : DecisionProcedure
Description : Experimental decision procedure for WS2S.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module DecisionProcedure (
   Term(..)
   , isValid
   , formula2Terms
   , unwindFixpoints
) where

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp

import qualified Debug.Trace as Dbg

type State = Int
type WS2STreeAut = TA.BATreeAutomaton State Alp.Symbol


-- |WS2S Lazy terms.
data Term =
   TStates WS2STreeAut [Alp.Variable] (Set.Set State)
   | TUnion Term Term
   | TIntersect Term Term
   | TCompl Term
   | TProj Alp.Variable Term
   | TMinusClosure Term (Set.Set Alp.Symbol)
   | TPair Term Term
   | TSet (Set.Set Term)
   deriving (Eq, Ord)

instance Show Term where
   show = showTerm


-- |Prints the term in human readable format.
showTerm (TSet set) = "{" ++ show set ++ "}"
showTerm (TPair t1 t2) = "(" ++ showTerm t1 ++ "," ++ showTerm t2 ++ ")"
showTerm (TMinusClosure t sym) = "(" ++ showTerm t ++ ") - {" ++ show sym ++ "}*"
showTerm (TProj var t) = "Proj_"++ show var ++ "( " ++ showTerm t ++ " )"
showTerm (TCompl t) = "¬(" ++ showTerm t ++ ")"
showTerm (TUnion t1 t2) = "(" ++ showTerm t1 ++ ") ∨ (" ++ showTerm t2 ++ ")"
showTerm (TIntersect t1 t2) = "(" ++ showTerm t1 ++ ") ∧ (" ++ showTerm t2 ++ ")"
showTerm (TStates _ _ st) = show st


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
minusSymbol t _ = error $ "minusSymbol: Minus symbol is defined only on term-pairs: " ++ show t


-- |Union set of terms -- defined only for a list of the form
-- [TSet a, TSet b, ..] and gives TSet (a union b union ...).
unionTerms :: [Term] -> Set.Set Term
unionTerms [] = Set.empty
unionTerms ((TSet a):xs) = Set.union a (unionTerms xs)


-- |Ominus for a set of symbols. Defined only for a term of the form (TSet a).
ominusSymbols :: Term -> Set.Set Alp.Symbol -> Term
ominusSymbols (TSet tset) sset = TSet (Set.fromList [minusSymbol (TPair t1 t2) s | s <- Set.toList sset, t1 <- Set.toList tset, t2 <- Set.toList tset])
ominusSymbols _ _ = error "ominusSymbols: Ominus is defined only on a set of terms"


-- |Fixpoint minus computation of the given term and a set of symbols.
fixpointComp :: Term -> Set.Set Alp.Symbol -> Term
--fixpointComp term@(TSet tset) sset | Dbg.trace ("fixpointComp " ++ show (term) ++ " ----- " ++ show (ominusSymbols term sset)) False = undefined
fixpointComp term@(TSet tset) sset =
   case ominusSymbols term sset of
      TSet modifset ->
         if Set.isSubsetOf modifset tset then term
         else fixpointComp (TSet $ Set.union modifset tset) sset
      _ -> error "fixpointComp: Ominus is defined only on a set of terms"
fixpointComp term sset = fixpointComp (TSet (Set.fromList [term])) sset


-- |Unwind fixpoints into sets of terms (corresponding to applying all fixpoints).
unwindFixpoints :: Term -> Term
unwindFixpoints t@(TStates _ _ _) = t
--unwindFixpoints (TMinusClosure t sset) | Dbg.trace ("unwindFixpoints " ++ show t ++ "------" ++ show sset) False = undefined
unwindFixpoints (TMinusClosure t sset) = fixpointComp (unwindFixpoints t) sset
unwindFixpoints (TUnion t1 t2) = TUnion (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TIntersect t1 t2) = TIntersect (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TCompl t) = TCompl (unwindFixpoints t)
unwindFixpoints (TProj var t) = TProj var (TSet $ Set.fromList [unwindFixpoints t])
unwindFixpoints _ = error "unwindFixpoints: Unwind is not defined for pair and minus terms"


-- |Test whether bottom is in the language of the term.
botIn :: Term -> Bool
botIn (TUnion t1 t2) = (botIn t1) || (botIn t2)
botIn (TIntersect t1 t2) = (botIn t1) && (botIn t2)
botIn (TCompl t) = not $ botIn t
botIn (TSet tset) =
   foldr gather False (Set.toList tset) where
      gather t b = (botIn t) || b
botIn (TProj _ t) = botIn t
botIn (TStates aut _ st) = (Set.intersection (TA.roots aut) st) /= Set.empty
botIn _ = error "botIn: Bottom membership is not defined"


-- |Convert formula to term representation. Uses additional information about
-- quantified variables reachable to a given term.
formula2TermsVars :: Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVars (Lo.FormulaAtomic atom) vars = atom2Terms atom
formula2TermsVars (Lo.Disj f1 f2) vars = TUnion (formula2TermsVars f1 vars) (formula2TermsVars f2 vars)
formula2TermsVars (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVars f1 vars) (formula2TermsVars f2 vars)
formula2TermsVars (Lo.Neg f) vars = TCompl (formula2TermsVars f vars)
formula2TermsVars (Lo.Exists var f) vars =
   TProj var (TMinusClosure (formula2TermsVars f (var:vars)) (Alp.projSymbolVars (Set.fromList [Alp.emptySymbol]) (var:vars)))
formula2TermsVars (Lo.ForAll _ _) _ = error "formula2TermsVars: Only formulas without forall are allowed"


-- |Convert atomic formula to term.
atom2Terms :: Lo.Atom -> Term
atom2Terms (Lo.Sing var) = TStates aut [var] (TA.leaves aut) where
   aut = sing var
atom2Terms (Lo.Cat v1 v2) = TStates aut [v1, v2] (TA.leaves aut) where
   aut = cat v1 v2


-- |Convert formula to term representation.
formula2Terms :: Lo.Formula -> Term
formula2Terms f = formula2TermsVars f []


-- |Decide whether given ground formula is valid.
isValid :: Lo.Formula -> Either Bool String
isValid f
   | Lo.freeVars f == [] = Left $ botIn $ unwindFixpoints $ formula2Terms (Lo.removeForAll f)
   | otherwise = Right "isValid: Only ground formula is allowed"

--------------------------------------------------------------------------------------------------------------
-- Part with the definitions of basic tree automata
--------------------------------------------------------------------------------------------------------------

singSymbol s x = ([s], Set.fromList [x])
catSymbol v1 v2 x1 x2 = ([v1,v2], Set.fromList [x1, x2])


-- |Tree automaton for an atomic predicate Sing(X).
sing :: Lo.Var -> WS2STreeAut
sing var = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([1,0], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '1' var)), Set.fromList [0])
      , (([0,1], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '0' var)), Set.fromList [1])])


-- |Tree automaton for an atomic predicate X=Y.L.
cat :: Lo.Var -> Lo.Var -> WS2STreeAut
cat v1 v2 = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (catSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (catSymbol '0' '1' v1 v2)), Set.fromList [1])
      , (([1,0], (catSymbol '1' '1' v1 v2)), Set.fromList [1])
      , (([1,0], (catSymbol '1' '0' v1 v2)), Set.fromList [0])])
