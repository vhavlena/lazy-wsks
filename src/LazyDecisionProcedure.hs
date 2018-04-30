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
botInLazy term@(TMinusClosure t sset) | Dbg.trace ("botInLazy: " ++ show term ++ "\n") False = undefined
botInLazy term@(TMinusClosure t sset) = (botInLazy t) || (if (isExpanded t) then False else (botInLazy (step term)))
botInLazy _ = error "botInLazy: Bottom membership is not defined"


-- |Fixpoint termination condition.
terminationCond :: Term -> Term -> Bool
terminationCond (TSet modif) (TSet term) = Set.isSubsetOf modif term
terminationCond (TIncrSet a _) t = terminationCond a t
terminationCond t (TIncrSet a _) = terminationCond t a
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


-- isExpandedIncr :: Term -> Bool
-- isExpandedIncr (TStates _ _ _) = True
-- isExpandedIncr (TMinusClosure t sset) = (isExpandedIncrCl t) && (terminationCond (ominusSymbolsLazy t sset) t)
-- isExpanded (TUnion t1 t2) = (isExpanded t1) && (isExpanded t2)
-- isExpanded (TIntersect t1 t2) = (isExpanded t1) && (isExpanded t2)
-- isExpanded (TCompl t) = isExpanded t
-- isExpanded (TProj _ t) = isExpanded t
-- isExpanded (TSet tset) =
--    foldr gather True (Set.toList tset) where
--       gather t b = (isExpanded t) && b
-- isExpanded (TIncrSet a _) = isExpanded a
--
--
-- isExpandedIncrCl (TSet _) = False
-- isExpandedIncrCl (TIncrSet a _) = isExpandedIncr a


-- |One step of all nested fixpoint computations. Returns modified term (fixpoints
-- are unwinded into TMinusClosure t)
step :: Term -> Term
step (TMinusClosure t sset) = TMinusClosure (TIncrSet complete incr) sset where
    st = step t
    incr = ominusSymbolsLazy st sset
    complete = unionTSets [incr, st]
step term@(TStates _ _ _) = term
step (TUnion t1 t2) = TIntersect (step t1) (step t2)
step (TIntersect t1 t2) = TIntersect (step t1) (step t2)
step (TCompl t) = TCompl (step t)
step (TProj a t) = TProj a (step t)
step (TSet tset) = TSet $ Set.fromList [step t | t <- Set.toList tset]
step (TIncrSet a b) = TIncrSet (step a) b


-- |Term ominus set of symbols for a lazy approach.
ominusSymbolsLazy :: Term -> Set.Set Alp.Symbol -> Term
ominusSymbolsLazy (TSet tset) sset = TSet (Set.fromList [minusSymbol (TPair t1 t2) s | s <- Set.toList sset, t1 <- Set.toList tset, t2 <- Set.toList tset])
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


isSubsumed :: [Term] -> Term -> Bool
isSubsumed [] _ = False
isSubsumed (x:xs) term@(TSet tset) = case x of
   (TSet sbset) -> if Set.isSubsetOf tset sbset then True
                   else isSubsumed xs term
   _ -> False


-- |Convert formula to lazy term representation (differs on using TIncrSet). Uses
-- additional information about quantified variables reachable to a given term.
formula2TermsVarsLazy :: Lo.Formula -> [Alp.Variable] -> Term
formula2TermsVarsLazy (Lo.FormulaAtomic atom) vars = atom2Terms atom
formula2TermsVarsLazy (Lo.Disj f1 f2) vars = TUnion (formula2TermsVarsLazy f1 vars) (formula2TermsVarsLazy f2 vars)
formula2TermsVarsLazy (Lo.Conj f1 f2) vars = TIntersect (formula2TermsVarsLazy f1 vars) (formula2TermsVarsLazy f2 vars)
formula2TermsVarsLazy (Lo.Neg f) vars = TCompl (formula2TermsVarsLazy f vars)
formula2TermsVarsLazy (Lo.Exists var f) vars =
   TProj var (TMinusClosure (TIncrSet innerTerm innerTerm) (Alp.projSymbolVars (Set.fromList [Alp.emptySymbol]) (var:vars))) where
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
