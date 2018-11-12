{-|
Module      : LazyDecisionProcedure
Description : Lazy decision procedure for WS2S.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module LazyDecisionProcedure (
   isValid
   , formula2Terms
) where


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified ComTreeAutomaton as CTA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp
import qualified StrictDecisionProcedure as SDP

import BaseDecisionProcedure
import BasicAutomata

import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with the lazy approach
--------------------------------------------------------------------------------------------------------------

-- |Lazy testing of bottom membership in the language of a given term.
botInLazy :: Term -> Bool
botInLazy (TTrue) = True
botInLazy (TUnion t1 t2) = (botInLazy t1) || (botInLazy t2)
botInLazy (TIntersect t1 t2) = (botInLazy t1) && (botInLazy t2)
botInLazy (TCompl t) = not $ botInLazy t
botInLazy (TSet tset) =
   foldr gather False (Set.toList tset) where
      gather t b = (botInLazy t) || b
botInLazy (TProj _ t) = botInLazy t
botInLazy (TStates aut _ st) = CTA.containsRoot aut st -- (Set.intersection (TA.roots aut) st) /= Set.empty
--botInLazy term@(TMinusClosure t sset) | Dbg.trace ("botInLazy: " ++ show t ++ "\n ... " ++ show (botInLazy t) ++ "\n\n") False = undefined
botInLazy term@(TMinusClosure t sset) = (botInLazy t) || (if isExpandedLight st then False else botInLazy st) where
  st = step term
botInLazy _ = error "botInLazy: Bottom membership is not defined"

--------------------------------------------------------------------------------------------------------------
-- Part with a checking whether term is expanded (plus removing fixpoints from terms).
--------------------------------------------------------------------------------------------------------------

-- |Remove subterms representing fixpoint computation, i.e., TIncrSet and TMinusClosure.
removeFixpoints :: Term -> Term
removeFixpoints (TUnion t1 t2) = TUnion (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TIntersect t1 t2) = TIntersect (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TCompl t) = TCompl $ removeFixpoints t
removeFixpoints (TProj var t) = TProj var (removeFixpoints t)
removeFixpoints (TMinusClosure t _) = removeFixpoints t
removeFixpoints (TPair t1 t2) = TPair (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TSet tset) = TSet $ Set.map (removeFixpoints) tset
removeFixpoints (TIncrSet t _) = removeFixpoints t
removeFixpoints t = t


-- |Lightweight check of a term expansion.
isExpandedLight :: Term -> Bool
isExpandedLight (TUnion t1 t2) = (isExpandedLight t1) && (isExpandedLight t2)
isExpandedLight (TIntersect t1 t2) = (isExpandedLight t1) && (isExpandedLight t2)
isExpandedLight (TCompl t) = isExpandedLight t
isExpandedLight (TProj _ t) = isExpandedLight t
isExpandedLight (TMinusClosure _ _) = False
isExpandedLight (TPair t1 t2) = (isExpandedLight t1) && (isExpandedLight t2)
isExpandedLight (TSet tset) = Set.foldr (&&) True (Set.map (isExpandedLight) tset)
isExpandedLight (TIncrSet t _) = isExpandedLight t
isExpandedLight t = True


-- |Test whether a given term is fully expanded. Uses incremental terms.
isExpandedIncr :: Term -> Bool
isExpandedIncr t = isSubsumedLazy (removeFixpoints $ step t) (removeFixpoints t)


--------------------------------------------------------------------------------------------------------------
-- Part with a fixpoint step functions
--------------------------------------------------------------------------------------------------------------

-- |One step of all nested fixpoint computations. Returns modified term (fixpoints
-- are unwinded into TMinusClosure t)
step :: Term -> Term --if (isExpandedIncr term) then (TMinusClosure t sset) else
step (TMinusClosure t sset) =
  if isSubsumedLazy incr strem then complete
  else TMinusClosure complete sset where
    st = step t
    strem = removeFixpoints st
    incr = removeRedundantTerms $ ominusSymbolsLazy strem sset
    complete = removeSet $ removeRedundantTerms $ unionTSets [incr, st]
step term@(TStates _ _ _) = term
step (TUnion t1 t2) = TUnion (step t1) (step t2)
step (TIntersect t1 t2) = TIntersect (step t1) (step t2)
step (TCompl t) = TCompl $ step t
step (TProj a t) = TProj a (step t)
step (TSet tset) = TSet $ Set.fromList [step t | t <- Set.toList tset]


-- |Term ominus set of symbols for a lazy approach.
ominusSymbolsLazy :: Term -> Set.Set Alp.Symbol -> Term
ominusSymbolsLazy (TSet tset) sset =  TSet $ Set.fromList [minusSymbol t1 t2 s | s <- Set.toList sset, t1 <- Set.toList tset, t2 <- Set.toList tset]
ominusSymbolsLazy (TMinusClosure t _) sset = ominusSymbolsLazy t sset
ominusSymbolsLazy t _ = error $ "ominusSymbolsLazy: Ominus is defined only on a set of terms: " ++ (show t)

--------------------------------------------------------------------------------------------------------------
-- Part with a term subsumption
--------------------------------------------------------------------------------------------------------------

-- |Structural term subsumption. Test whether the first term is subsumed by
-- the second term. Now it is implemented on the structural level.
isSubsumedLazy :: Term -> Term -> Bool
isSubsumedLazy (TUnion t1 t2) (TUnion t3 t4) = (isSubsumedLazy t1 t3) && (isSubsumedLazy t2 t4)
isSubsumedLazy (TIntersect t1 t2) (TIntersect t3 t4) = (isSubsumedLazy t1 t3) && (isSubsumedLazy t2 t4)
isSubsumedLazy (TCompl t1) (TCompl t2) = isSubsumedLazy t2 t1
isSubsumedLazy (TProj v1 t1) (TProj v2 t2)
  | v1 == v2 = isSubsumedLazy t1 t2
  | otherwise = False
isSubsumedLazy (TSet tset1) (TSet tset2) = foldr (&&) True ((Set.toList tset1) >>= (\a -> return $ any (isSubsumedLazy a) lst))
  where
    lst = Set.toList tset2
isSubsumedLazy (TStates aut1 var1 st1) (TStates aut2 var2 st2) = (aut1 == aut2) && (var1 == var2) && (subsetSetStates st1 st2)
isSubsumedLazy t1 (TMinusClosure t2 sym) = isSubsumedLazy t1 t2
isSubsumedLazy _ _ = False


-- |Remove redundant terms from a given set of terms. The subsumption is not
-- partial order (we can have a<=b and b<=a and a!=b). Therefore, we may not remove
-- all terms from a set.
removeRedundantTerms :: Term -> Term
removeRedundantTerms (TSet tset) = TSet $ Set.fromList reduced
    where
      lst = Set.toList $ Set.map (removeRedundantTerms) tset
      reduced = removeSubSet lst lst
removeRedundantTerms (TProj v t) = TProj v (removeRedundantTerms t)
removeRedundantTerms (TCompl t) = TCompl $ removeRedundantTerms t
removeRedundantTerms (TMinusClosure t sset) = TMinusClosure (removeRedundantTerms t) sset
removeRedundantTerms t = t


removeSubSet :: [Term] -> [Term] -> [Term]
removeSubSet [] _ = []
removeSubSet (a:lst) pat =
  if List.any (isSubsumedLazy a) del then removeSubSet lst del
  else a:(removeSubSet lst pat)
  where
    del = List.delete a pat


--------------------------------------------------------------------------------------------------------------
-- Part with a conversion logic formula to lazy terms
--------------------------------------------------------------------------------------------------------------

-- |Convert formula to lazy term representation (differs on using TIncrSet). Uses
-- additional information about quantified variables reachable to a given term.
formula2TermsVarsLazy :: MonaAutDict -> Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVarsLazy autdict (Lo.FormulaAtomic atom) vars = atom2Terms autdict atom
formula2TermsVarsLazy autdict (Lo.Disj f1 f2) vars = TUnion (formula2TermsVarsLazy autdict f1 vars)
  (formula2TermsVarsLazy autdict f2 vars)
formula2TermsVarsLazy autdict (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVarsLazy autdict f1 vars)
  (formula2TermsVarsLazy autdict f2 vars)
formula2TermsVarsLazy autdict (Lo.Neg f) vars = TCompl $ formula2TermsVarsLazy autdict f vars
formula2TermsVarsLazy autdict (Lo.Exists var f) vars =
   TProj var (TMinusClosure innerTerm (Alp.projZeroSymbol (var:vars))) where
      innerTerm = TSet $ Set.fromList [formula2TermsVarsLazy autdict f (var:vars)]
formula2TermsVarsLazy _ (Lo.ForAll _ _) _ = error "formula2TermsVarsLazy: Only formulas without forall are allowed"


-- |Convert formula to term representation.
formula2Terms :: MonaAutDict -> Lo.Formula -> Term
formula2Terms autdict f =  formula2TermsVarsLazy autdict f []


-- |Decide whether given ground formula is valid (lazy approach).
isValid :: MonaAutDict -> Lo.Formula -> Either Bool String
isValid autdict f
   | Lo.freeVars f == [] = Left $ botInLazy $ formula2Terms autdict f
   | otherwise = Right $ "isValidLazy: Only ground formula is allowed" ++ show (Lo.freeVars f)
