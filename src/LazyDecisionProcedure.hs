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
import qualified TreeAutomaton as TA
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
botInLazy (TUnion t1 t2) = (botInLazy t1) || (botInLazy t2)
botInLazy (TIntersect t1 t2) = (botInLazy t1) && (botInLazy t2)
botInLazy (TCompl t) = not $ botInLazy t
botInLazy (TSet tset) =
   foldr gather False (Set.toList tset) where
      gather t b = (botInLazy t) || b
botInLazy (TIncrSet a b) = botInLazy b
botInLazy (TProj _ t) = botInLazy t
botInLazy (TStates aut _ st) = (Set.intersection (TA.roots aut) st) /= Set.empty
botInLazy term@(TMinusClosure t sset) | Dbg.trace ("botInLazy: " ++ show term ++ "\n" ++ show (isExpandedIncr t)) False = undefined
botInLazy term@(TMinusClosure t sset) = (botInLazy t) || (if (isExpandedIncr t) then False else (botInLazy (step term)))
botInLazy _ = error "botInLazy: Bottom membership is not defined"


-- |Fixpoint termination condition.
terminationCond :: Term -> Term -> Bool
terminationCond t1@(TSet modif) t2@(TSet term) = if (modif == (Set.empty)) then False else Set.isSubsetOf modif term
--terminationCond (TIncrSet a _) t = terminationCond a t
--terminationCond t (TIncrSet a _) = terminationCond t a
terminationCond t1 t2 = error $ "terminationCond: Not defined" ++ (show t1) ++ (show t2)


-- |Test whether a given term is fully expanded (i.e., all fixpoints are expanded).
isExpanded :: Term -> Bool
isExpanded (TStates _ _ _) = True
isExpanded (TMinusClosure t sset) = (isExpanded t) && (terminationCond (ominusSymbolsLazy t sset) t)
isExpanded (TUnion t1 t2) = (isExpanded t1) && (isExpanded t2)
isExpanded (TIntersect t1 t2) = (isExpanded t1) && (isExpanded t2)
isExpanded (TCompl t) = isExpanded t
isExpanded (TProj _ t) = isExpanded t
isExpanded (TSet tset) =
   foldr gather True (Set.toList tset) where
      gather t b = (isExpanded t) && b
isExpanded (TIncrSet a _) = isExpanded a


-- |Recursively remove incremental terms. Necessary for checking term inclusion
-- (bottom check).
removeIncrTerm :: Term -> Term
removeIncrTerm (TUnion t1 t2) = TUnion (removeIncrTerm t1) (removeIncrTerm t2)
removeIncrTerm (TIntersect t1 t2) = TIntersect (removeIncrTerm t1) (removeIncrTerm t2)
removeIncrTerm (TCompl t) = TCompl (removeIncrTerm t)
removeIncrTerm (TProj var t) = TProj var (removeIncrTerm t)
removeIncrTerm (TMinusClosure t sset) = TMinusClosure (removeIncrTerm t) sset
removeIncrTerm (TPair t1 t2) = TPair (removeIncrTerm t1) (removeIncrTerm t2)
removeIncrTerm (TSet tset) = TSet (Set.map (removeIncrTerm) tset)
removeIncrTerm (TIncrSet t incr) = removeIncrTerm t
removeIncrTerm t = t


-- |Test whether a given term is fully expanded. Uses incremental terms.
isExpandedIncr :: Term -> Bool
isExpandedIncr (TStates _ _ _) = True
isExpandedIncr (TMinusClosure t sset) = isExpandedIncr t
isExpandedIncr (TUnion t1 t2) = (isExpandedIncr t1) && (isExpandedIncr t2)
isExpandedIncr (TIntersect t1 t2) = (isExpandedIncr t1) && (isExpandedIncr t2)
isExpandedIncr (TCompl t) = isExpandedIncr t
isExpandedIncr (TProj _ t) = isExpandedIncr t
isExpandedIncr (TSet tset) =
   foldr gather True (Set.toList tset) where
      gather t b = (isExpandedIncr t) && b
isExpandedIncr (TIncrSet a b) = (isExpandedIncr a) && (terminationCond b (removeIncrTerm a))


removeFixpoints :: Term -> Term
removeFixpoints (TUnion t1 t2) = TUnion (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TIntersect t1 t2) = TIntersect (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TCompl t) = TCompl (removeFixpoints t)
removeFixpoints (TProj var t) = TProj var (removeFixpoints t)
removeFixpoints (TMinusClosure t sset) = removeFixpoints t
removeFixpoints (TPair t1 t2) = TPair (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TSet tset) = TSet (Set.map (removeFixpoints) tset)
removeFixpoints (TIncrSet t incr) = removeFixpoints t
removeFixpoints t = t

-- |One step of all nested fixpoint computations. Returns modified term (fixpoints
-- are unwinded into TMinusClosure t)
step :: Term -> Term --if (isExpandedIncr term) then (TMinusClosure t sset) else
step term@(TMinusClosure t sset) = if (isExpandedIncr newTerm) then (TIncrSet (removeFixpoints complete) incr) else TMinusClosure newTerm sset where
    st = step t
    incr = removeRedundantTerms $ ominusSymbolsLazy st sset
    complete = removeRedundantTerms $ unionTSets [incr, st]
    newTerm = (TIncrSet complete incr)
step term@(TStates _ _ _) = term
step (TUnion t1 t2) = TIntersect (step t1) (step t2)
step (TIntersect t1 t2) = TIntersect (step t1) (step t2)
step (TCompl t) = TCompl (step t)
step (TProj a t) = TProj a (step t)
step (TSet tset) =  TSet $ Set.fromList [step t | t <- Set.toList tset]
step (TIncrSet a b) = TIncrSet (step a) b


-- |Term ominus set of symbols for a lazy approach.
ominusSymbolsLazy :: Term -> Set.Set Alp.Symbol -> Term
ominusSymbolsLazy (TSet tset) sset =  TSet (Set.fromList [minusSymbol (TPair t1 t2) s | s <- Set.toList sset, t1 <- Set.toList tset, t2 <- Set.toList tset])
ominusSymbolsLazy (TMinusClosure t _) sset = ominusSymbolsLazy t sset
ominusSymbolsLazy (TIncrSet a b) sset = ominusSymbolsLazy a sset
ominusSymbolsLazy t _ = error $ "ominusSymbolsLazy: Ominus is defined only on a set of terms: " ++ (show t)


-- |Fixpoint computation for a lazy approach. Simultaneously with every step
-- check bottom membership.
fixpointCompLazy :: Term -> Set.Set Alp.Symbol -> Bool
--fixpointCompLazy term@(TSet tset) sset | Dbg.trace ("fixpointCompLazy " ++ show term ++ "------" ++ show sset) False = undefined
fixpointCompLazy term@(TSet tset) sset =
   case ominusSymbolsLazy term sset of
      TSet modifset ->
         if Set.isSubsetOf modifset tset then False
         else (botInLazy $ TSet modifset) || (fixpointCompLazy (TSet $ Set.fromList $ filter (isSubsumed slist) slist) sset)
            where
               slist = Set.toList (Set.union modifset tset)
      _ -> error "fixpointComp: Ominus is defined only on a set of terms"
fixpointCompLazy term sset = fixpointCompLazy (TSet (Set.fromList [term])) sset


-- |Very basic term subsumption based only on one-level subset.
isSubsumed :: [Term] -> Term -> Bool
isSubsumed [] _ = False
isSubsumed (x:xs) term@(TSet tset) = case x of
   (TSet sbset) -> if Set.isSubsetOf tset sbset then True
                   else isSubsumed xs term
   _ -> False


-- |Structural term subsumption. Test whether the first term is subsumed by
-- the second term. Now it is implemented on the structural level.
-- TODO: incomplete
isSubsumedLazy :: Term -> Term -> Bool
isSubsumedLazy (TUnion t1 t2) (TUnion t3 t4) = (isSubsumedLazy t1 t3) && (isSubsumedLazy t2 t4)
isSubsumedLazy (TIntersect t1 t2) (TIntersect t3 t4) = (isSubsumedLazy t1 t3) && (isSubsumedLazy t2 t4)
isSubsumedLazy (TCompl t1) (TCompl t2) = isSubsumedLazy t1 t2
isSubsumedLazy (TProj v1 t1) (TProj v2 t2)
  | v1 == v2 = isSubsumedLazy t1 t2
  | otherwise = (v1 < v2)
isSubsumedLazy (TSet tset1) (TSet tset2) = foldr (&&) True ((Set.toList tset1) >>= (\a -> return (any (isSubsumedLazy a) lst)))
  where
    lst = Set.toList tset2
isSubsumedLazy (TMinusClosure t1 sset1) (TMinusClosure t2 sset2) = (isSubsumedLazy t1 t2) && ((length sset1) <= (length sset2))
isSubsumedLazy (TStates aut1 var1 st1) (TStates aut2 var2 st2) = (aut1 == aut2) && (var1 == var2) && (st1 == st2)
isSubsumedLazy (TIncrSet t1 in1) (TIncrSet t2 in2) = (isSubsumedLazy t1 t2) && (isSubsumedLazy in1 in2)
--isSubsumedLazy (TMinusClosure t1 sset1) t2 = isSubsumedLazy t1 t2
isSubsumedLazy t1 t2 = False
--isSubsumedLazy t1 t2 = error $ "Incompatible types: isSubsumedLazy " ++ (show t1) ++ "\n***\n" ++ (show t2)


-- |Remove redundant terms from a given set of terms. The subsumption is not
-- partial order (we can have a<=b and b<=a and a!=b). Therefore, we may not remove
-- all terms from a set.
removeRedundantTerms :: Term -> Term
--removeRedundantTerms t@(TSet tset) | Dbg.trace ("removeRedundantTerms: " ++ show t ++ "\n" ++ show (TSet $ Set.fromList $ ((Set.toList tset) >>= (\a -> if (any (isSubsumedLazy a) (List.delete a (Set.toList tset))) then [] else [a])))) False = undefined
removeRedundantTerms (TSet tset) = TSet $ Set.fromList $ if (not $ Set.null tset) && (null reduced) then [head lst] else reduced
    where
      lst = Set.toList $ Set.map (removeRedundantTerms) tset
      reduced = lst >>= (\a -> if (any (isSubsumedLazy a) (List.delete a lst)) then [] else [a])
removeRedundantTerms (TProj v t) = TProj v (removeRedundantTerms t)
removeRedundantTerms (TCompl t) = TCompl (removeRedundantTerms t)
removeRedundantTerms (TMinusClosure t sset) = TMinusClosure (removeRedundantTerms t) sset
removeRedundantTerms (TIncrSet t1 t2) = TIncrSet (removeRedundantTerms t1) (removeRedundantTerms t2)
removeRedundantTerms t = t
removeRedundantTerms t = error $ "removeRedundantTerms " ++ (show t)


-- |Convert formula to lazy term representation (differs on using TIncrSet). Uses
-- additional information about quantified variables reachable to a given term.
formula2TermsVarsLazy :: Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVarsLazy (Lo.FormulaAtomic atom) vars = atom2Terms atom
formula2TermsVarsLazy (Lo.Disj f1 f2) vars = TUnion (formula2TermsVarsLazy f1 vars) (formula2TermsVarsLazy f2 vars)
formula2TermsVarsLazy (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVarsLazy f1 vars) (formula2TermsVarsLazy f2 vars)
formula2TermsVarsLazy (Lo.Neg f) vars = TCompl (formula2TermsVarsLazy f vars)
formula2TermsVarsLazy (Lo.Exists var f) vars =
   TProj var (TMinusClosure (TIncrSet innerTerm (TSet Set.empty)) (Alp.projSymbolVars (Set.fromList [Alp.emptySymbol]) (var:vars))) where
     innerTerm = TSet (Set.fromList [formula2TermsVarsLazy f (var:vars)])
formula2TermsVarsLazy (Lo.ForAll _ _) _ = error "formula2TermsVarsLazy: Only formulas without forall are allowed"


-- |Convert formula to term representation.
formula2Terms :: Lo.Formula -> Term
formula2Terms f = formula2TermsVarsLazy f []


-- |Decide whether given ground formula is valid (lazy approach).
isValid :: Lo.Formula -> Either Bool String
isValid f
   | Lo.freeVars f == [] = Left $ botInLazy $ formula2Terms (Lo.removeForAll f)
   | otherwise = Right "isValidLazy: Only ground formula is allowed"
