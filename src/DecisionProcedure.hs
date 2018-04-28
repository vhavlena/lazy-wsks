{-|
Module      : DecisionProcedure
Description : Experimental decision procedure for WS2S.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module DecisionProcedure (
   Term(..)
   , isValid
   , isValidLazy
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
showTermDbg ind (TIncrSet a b) = (showTermDbg ind a) ++ "---" ++ (showTermDbg ind b)


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
minusSymbol (TPair (TIncrSet a _) (TIncrSet b _)) sym = minusSymbol (TPair a b) sym
minusSymbol (TPair (TIncrSet a _) b) sym = minusSymbol (TPair a b) sym
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
unwindFixpoints (TMinusClosure t sset) = fixpointComp (unwindFixpoints t) sset
unwindFixpoints (TUnion t1 t2) = TUnion (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TIntersect t1 t2) = TIntersect (unwindFixpoints t1) (unwindFixpoints t2)
unwindFixpoints (TCompl t) = TCompl (unwindFixpoints t)
unwindFixpoints (TProj var t) = TProj var (TSet $ Set.fromList [unwindFixpoints t])
unwindFixpoints (TSet tset) = TSet $ Set.fromList[unwindFixpoints t | t <- Set.toList tset]
unwindFixpoints t = error ("unwindFixpoints: Unwind is not defined for pair and minus terms" ++ (show t))


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
   TProj var (TMinusClosure (TSet (Set.fromList [formula2TermsVars f (var:vars)])) (Alp.projSymbolVars (Set.fromList [Alp.emptySymbol]) (var:vars)))
formula2TermsVars (Lo.ForAll _ _) _ = error "formula2TermsVars: Only formulas without forall are allowed"


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


-- |Convert formula to term representation.
formula2Terms :: Lo.Formula -> Term
formula2Terms f = formula2TermsVars f []


-- |Decide whether given ground formula is valid (strict approach).
isValid :: Lo.Formula -> Either Bool String
isValid f
   | Lo.freeVars f == [] = Left $ botIn $ unwindFixpoints $ formula2Terms (Lo.removeForAll f)
   | otherwise = Right "isValid: Only ground formula is allowed"

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
--botInLazy term@(TMinusClosure t sset) | Dbg.trace ("botInLazy: " ++ show term ++ "\n") False = undefined
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


-- |One step of all nested fixpoint computations. Returns modified term (fixpoints
-- are unwinded into TMinusClosure t)
step :: Term -> Term
step (TMinusClosure t sset) =
  let st = step t
      incr = ominusSymbolsLazy st sset in case t of
        (TSet a) ->  TMinusClosure (TIncrSet (unionTSets [incr, st]) incr) sset
        (TIncrSet a b) -> TMinusClosure (TIncrSet complete incr) sset where
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


-- |Decide whether given ground formula is valid (lazy approach).
isValidLazy :: Lo.Formula -> Either Bool String
isValidLazy f
   | Lo.freeVars f == [] = Left $ botInLazy $ formula2Terms (Lo.removeForAll f)
   | otherwise = Right "isValidLazy: Only ground formula is allowed"

--------------------------------------------------------------------------------------------------------------
-- Part with the definitions of basic tree automata
--------------------------------------------------------------------------------------------------------------

singSymbol s x = ([s], Set.fromList [x])
pairSymbol v1 v2 x1 x2 = ([v1,v2], Set.fromList [x1, x2])


-- |Tree automaton for an atomic predicate Sing(X).
singAut :: Lo.Var -> WS2STreeAut
singAut var = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([1,0], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '1' var)), Set.fromList [0])
      , (([0,1], (singSymbol '0' var)), Set.fromList [0])
      , (([1,1], (singSymbol '0' var)), Set.fromList [1])])


-- |Tree automaton for an atomic predicate X=Y.L.
catAut :: Lo.Var -> Lo.Var -> WS2STreeAut
catAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [1])
      , (([1,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [1])
      , (([1,0], (pairSymbol '1' '0' v1 v2)), Set.fromList [0])])


-- |Tree automaton for atomic predicate X subseteq Y
subseteqAut :: Lo.Var -> Lo.Var -> WS2STreeAut
subseteqAut v1 v2 = TA.BATreeAutomaton (Set.fromList [0]) (Set.fromList [0]) (Set.fromList [0])
   (Map.fromList[ (([0,0], (pairSymbol '0' '0' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '0' '1' v1 v2)), Set.fromList [0])
      , (([0,0], (pairSymbol '1' '1' v1 v2)), Set.fromList [0])])


-- |Tree automaton for atomic predicat X=eps
epsAut :: Lo.Var -> WS2STreeAut
epsAut var = TA.BATreeAutomaton (Set.fromList [0, 1]) (Set.fromList [0]) (Set.fromList [1])
   (Map.fromList[ (([1,1], (singSymbol '1' var)), Set.fromList [0])
      , (([0,0], (singSymbol '0' var)), Set.fromList [0])])
