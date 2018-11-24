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
import BaseProcedureSymbolic
import BasicAutomata
import Control.Exception.Assert

import qualified Debug.Trace as Dbg

type Cache = Map.Map (Term, Term, Alp.Symbol) Term


--------------------------------------------------------------------------------------------------------------
-- Part with the lazy approach
--------------------------------------------------------------------------------------------------------------

-- |Lazy testing of bottom membership in the language of a given term.
botInLazy :: Term -> Cache -> Bool
botInLazy (TTrue) _ = True
botInLazy (TFalse) _ = False
botInLazy (TUnion t1 t2) m = (botInLazy t1 m) || (botInLazy t2 m)
botInLazy (TIntersect t1 t2) m = (botInLazy t1 m) && (botInLazy t2 m)
botInLazy (TCompl t) m = not $ botInLazy t m
botInLazy (TSet tset) m =
   foldr gather False (Set.toList tset) where
      gather t b = (botInLazy t m) || b
botInLazy (TProj _ t) m = botInLazy t m
botInLazy (TStates aut _ st) _ = CTA.containsRoot aut st -- (Set.intersection (TA.roots aut) st) /= Set.empty
--botInLazy term@(TMinusClosure t _ sset) m | Dbg.trace ("botInLazy: " ++ show (term) ++ "\n ... ") False = undefined
botInLazy term@(TMinusClosure t _ sset) m = (botInSub t True) || (if isExpandedLight st then (botInSub st True) else botInLazy st m) where
  st= step term
botInLazy _ _ = error "botInLazy: Bottom membership is not defined"


-- |Bottom membership in the language of a given term.
botInSub :: Term -> Bool -> Bool
botInSub (TTrue) _ = True
botInSub (TUnion t1 t2) l = (botInSub t1 l) || (botInSub t2 l)
botInSub (TIntersect t1 t2) l = (botInSub t1 l) && (botInSub t2 l)
botInSub (TCompl t) l = not $ botInSub t (not l)
--botInSub (TSet tset) | Dbg.trace ("botInLazy: " ++ show (length $ Set.toList tset) ++ "\n ... ") False = undefined
botInSub (TSet tset) l =
   foldr gather False (Set.toList tset) where
      gather t b = (botInSub t l) || b
botInSub (TProj _ t) l = botInSub t l
botInSub (TStates aut _ st) l = CTA.containsRoot aut st
botInSub term@(TMinusClosure t _ sset) l = if l then (botInSub t l) else (not l)
botInSub _ _ = error "botInSub: Bottom membership is not defined"

--------------------------------------------------------------------------------------------------------------
-- Part with a checking whether term is expanded (plus removing fixpoints from terms).
--------------------------------------------------------------------------------------------------------------

-- |Remove subterms representing fixpoint computation, i.e., TIncrSet and TMinusClosure.
removeFixpoints :: Term -> Term
removeFixpoints (TUnion t1 t2) = TUnion (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TIntersect t1 t2) = TIntersect (removeFixpoints t1) (removeFixpoints t2)
removeFixpoints (TCompl t) = TCompl $ removeFixpoints t
removeFixpoints (TProj var t) = TProj var (removeFixpoints t)
removeFixpoints (TMinusClosure t _ _) = removeFixpoints t
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
isExpandedLight (TMinusClosure _ _ _) = False
isExpandedLight (TPair t1 t2) = (isExpandedLight t1) && (isExpandedLight t2)
isExpandedLight (TSet tset) = Set.foldr (&&) True (Set.map (isExpandedLight) tset)
isExpandedLight (TIncrSet t _) = isExpandedLight t
isExpandedLight t = True


--------------------------------------------------------------------------------------------------------------
-- Part with a fixpoint step functions
--------------------------------------------------------------------------------------------------------------

-- |One step of all nested fixpoint computations. Returns modified term (fixpoints
-- are unwinded into TMinusClosure t)
step :: Term -> Term  --if (isExpandedIncr term) then (TMinusClosure t sset) else
--step (TMinusClosure (TSet t) inc sset) cache | Dbg.trace ("minus: " ++ (show $ length $ Set.toList t) ++ "\n " ) False = undefined
step (TMinusClosure t inc sset) =
  if isSubsumedLazy incr strem then complete
  else TMinusClosure complete strem sset where
    st = step t
    strem = removeRedundantTerms $ removeFixpoints st
    inc' = differenceTSets strem inc
    ret = ominusSymbolsLazySym strem inc' sset
    ret2 = ominusSymbolsLazy strem inc' (Alp.unwindSymbolsX sset)
    incr = if ret == ret2 then (removeRedundantTerms $ ret) else error $ (show ret) ++ "\n "++(show ret2) ++ (show sset) ++ (show strem) ++ (show inc')
    --incr = removeRedundantTerms $ ret
    complete = removeRedundantTerms $ unionTSets [incr, st]
step term@(TStates _ _ _) = term
step (TUnion t1 t2) = TUnion (step t1) (step t2)
step (TIntersect t1 t2) = TIntersect (step t1) (step t2)
step (TCompl t) = TCompl $ step t
step (TProj a t) = TProj a (step t)
step (TSet tset)= TSet $ Set.fromList [step t | t <- Set.toList tset]
step (TTrue) = TTrue


-- step :: Term -> Cache -> (Term, Cache)  --if (isExpandedIncr term) then (TMinusClosure t sset) else
-- --step (TMinusClosure (TSet t) inc sset) cache | Dbg.trace ("minus: " ++ (show $ length $ Set.toList t) ++ "\n " ) False = undefined
-- step (TMinusClosure t inc sset) cache =
--   if isSubsumedLazy incr strem then (complete, mp)
--   else (TMinusClosure complete strem sset, mp) where
--     (st, p) = step t cache
--     strem = removeRedundantTerms $ removeFixpoints st
--     inc' = differenceTSets strem inc
--     (ret, mp) = ominusSymbolsLazy strem inc' sset p
--     incr = removeRedundantTerms $ ret
--     complete = removeRedundantTerms $ unionTSets [incr, st]
-- step term@(TStates _ _ _) c = (term, c)
-- step (TUnion t1 t2) c = (TUnion r1 r2, Map.union m1 m2) where
--   (r1,m1) = (step t1 c)
--   (r2,m2) = (step t2 m1)
-- step (TIntersect t1 t2) c = (TIntersect r1 r2, Map.union m1 m2) where
--   (r1,m1) = (step t1 c)
--   (r2,m2) = (step t2 m1)
-- step (TCompl t) c = (TCompl r1, m1) where
--   (r1,m1) = (step t c)
-- step (TProj a t) c = (TProj a r1, m1) where
--   (r1,m1) = (step t c)
-- step (TSet tset) c = (TSet $ Set.fromList r1, m1) where
--   (r1,m1) = foldr (\(a,b) (c,d) -> (a:c, Map.union b d)) ([], Map.empty) [step t c | t <- Set.toList tset]
-- step (TTrue) m = (TTrue, m)


-- |Term ominus set of symbols for a lazy approach.
ominusSymbolsLazy :: Term -> Term -> Set.Set Alp.Symbol -> Term
ominusSymbolsLazy (TSet tset) (TSet inc) sset = TSet $ Set.fromList om where
  --tset' = tset
  iter = Set.union (Set.cartesianProduct tset inc) (Set.cartesianProduct inc tset)
  om = [minusSymbol t1 t2 s | s <- Set.toList sset, (t1, t2) <- Set.toList iter]
ominusSymbolsLazy t _ _ = error $ "ominusSymbolsLazy: Ominus is defined only on a set of terms: " ++ (show t)



ominusSymbolsLazySym :: Term -> Term -> Set.Set Alp.Symbol -> Term
ominusSymbolsLazySym (TSet tset) (TSet inc) sset = TSet $ Set.fromList flatom where
  iter = Set.union (Set.cartesianProduct tset inc) (Set.cartesianProduct inc tset)
  om = [forgetFle $ minusSymbolSym t1 t2 sset | (t1, t2) <- Set.toList iter]
  flatom = foldr (++) [] om


-- |Minus symbol with memoizing.
minusSymbol' mp t1 t2 s = case Map.lookup (t1, t2, s) mp of
  Nothing -> (t,[((t1,t2,s),t)]) where
    t = minusSymbol t1 t2 s
  Just val -> (val, [])

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
isSubsumedLazy t1 (TMinusClosure t2 _ sym) = isSubsumedLazy t1 t2
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
removeRedundantTerms (TMinusClosure t inc sset) = TMinusClosure (removeRedundantTerms t) inc sset
removeRedundantTerms t = t


-- |Removed subsumed items from a list. Note that the subsumption is preorder and
-- hence there can be cyclic dependency (a < b and b < a). In this case it is NOT
-- possible to remove both a and b.
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
   TProj var (TMinusClosure innerTerm (sinkTerm) (Alp.projXZeroSymbol (var:vars))) where
      innerTerm = TSet $ Set.fromList [formula2TermsVarsLazy autdict f (var:vars)]
formula2TermsVarsLazy _ (Lo.ForAll _ _) _ = error "formula2TermsVarsLazy: Only formulas without forall are allowed"


-- |Convert formula to term representation.
formula2Terms :: MonaAutDict -> Lo.Formula -> Term
formula2Terms autdict f =  formula2TermsVarsLazy autdict f []


-- |Decide whether given ground formula is valid (lazy approach).
isValid :: MonaAutDict -> Lo.Formula -> Either Bool String
--isValid autdict f | Dbg.trace ("isValid: " ++ show (formula2Terms autdict f)) False = undefined
isValid autdict f
   | Lo.freeVars f == [] = Left $ botInLazy  (formula2Terms autdict f) Map.empty
   | otherwise = Right $ "isValidLazy: Only ground formula is allowed" ++ show (Lo.freeVars f)
