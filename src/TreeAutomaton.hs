{-|
Module      : TreeAutomaton
Description : Very basic operations with tree automata (not efficient).
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module TreeAutomaton (
   BATreeAutomaton(..)
   , Transition
   , Transitions
   , pre
   , removeUnreachable
   , autRestriction
) where

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified AuxFunctions as Aux
import qualified Alphabet as Alp

-- |Type for single transition and a transition function
type Transitions a b = Map.Map ([a],b) (Set.Set a)
type Transition a b = (([a],b), Set.Set a)
type SimplTransition a = ([a],a)
type SimplTransitionRev a = (a,a)

-- |Bottom-up tree automaton
data BATreeAutomaton a b = BATreeAutomaton {
   states :: Set.Set a
   , roots :: Set.Set a
   , leaves :: Set.Set a
   , transitions :: Transitions a b
}

-- |Formatted output of BA
instance (Show a, Show b) => Show (BATreeAutomaton a b) where
  show (BATreeAutomaton st rt lv tr) = "States: " ++ Aux.prArr "," (Set.toList st) ++
    "\n" ++ "Roots: " ++ Aux.prArr "," (Set.toList rt) ++ "\n" ++ "Leaves: " ++
    Aux.prArr "," (Set.toList lv) ++ "\n" ++ "Transitions: \n" ++
    intercalate "\n" ( map (printTrans) (Map.toList tr))


-- |Print single transition (convert to String)
printTrans :: (Show a, Show b) => Transition a b -> String
printTrans ((a,b),c) = "(" ++ (Aux.prArr "," a) ++ ";" ++ (show b) ++ ") -> " ++
  "{" ++ (Aux.prArr "," (Set.toList c)) ++ "}"


-- |Syntax equivalence of two tree automata.
instance (Eq m, Eq n) => Eq (BATreeAutomaton m n) where
   BATreeAutomaton st1 rt1 lv1 tr1 == BATreeAutomaton st2 rt2 lv2 tr2 =
      (st1 == st2) && (rt1 == rt2) && (lv1 == lv2) && (tr1 == tr2)

-- |Syntax ordering of two tree automata.
instance (Ord m, Ord n) => Ord (BATreeAutomaton m n) where
   BATreeAutomaton st1 rt1 lv1 tr1 <= BATreeAutomaton st2 rt2 lv2 tr2 =
      (st1 <= st2) && (rt1 <= rt2) && (lv1 <= lv2) && (tr1 <= tr2)


-- |Pre (Up) of a set of states wrt given symbol.
pre :: (Ord a, Ord b) => BATreeAutomaton a b -> [Set.Set a] -> b -> Set.Set a
pre (BATreeAutomaton _ _ _ tr) st sym = foldr (Set.union) Set.empty [Map.findWithDefault Set.empty (s,sym) tr | s <- crossProd st ]


simplifyTrans :: (Ord a) => [Transition a b] -> [SimplTransition a]
simplifyTrans trans = Set.toList $ Set.fromList (trans >>= \((x,_),y) -> Set.toList y >>= \z -> return (x,z))


reverseSimplified :: [SimplTransition a] -> [SimplTransitionRev a]
reverseSimplified tr = tr >>= \(x,y) -> x >>= \z -> return (y,z)

downReachStep :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
downReachStep states trans = Set.fromList $ ((Set.toList states) >>= \x -> (Set.toList $ Map.findWithDefault Set.empty x trans) )


downReach :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
downReach states trans = if Set.isSubsetOf states' states then states else downReach (Set.union states states') trans where
  states' = downReachStep states trans


toSingleton :: [(a,b)] -> [(a,Set.Set b)]
toSingleton = map (\(x,y) -> (x, Set.singleton y))


upReachStep :: (Ord a) => Set.Set a -> [([a],a)] -> Set.Set a
upReachStep states trans = Set.fromList $ (trans >>= \(x,y) -> if Set.isSubsetOf (Set.fromList x) states then return y else [])

upReach :: (Ord a) => Set.Set a -> [SimplTransition a] -> Set.Set a
upReach states trans = if Set.isSubsetOf states' states then states else upReach (Set.union states states') trans where
  states' = upReachStep states trans


transProj :: (Ord a) => Set.Set a -> [Transition a b] -> [Transition a b]
transProj states trans = trans >>= \t@((x,_),y) -> if (Set.isSubsetOf (Set.fromList x) states) && (Set.isSubsetOf y states) then return t else []


autRestriction :: (Ord a, Ord b) => Set.Set a -> BATreeAutomaton a b -> BATreeAutomaton a b
autRestriction states (BATreeAutomaton st rt lv tr) = BATreeAutomaton states newrt newlv newtr where
  newrt = Set.intersection states rt
  newlv = Set.intersection states lv
  newtr = Map.fromList $ transProj states (Map.toList tr)


removeUnreachable :: (Ord a, Ord b) => BATreeAutomaton a b -> BATreeAutomaton a b
removeUnreachable aut@(BATreeAutomaton st rt lv tr) = autRestriction newst aut where
  simple = simplifyTrans $ Map.toList $ tr
  simple' = Map.fromListWith (Set.union) (toSingleton $ reverseSimplified $ simple)
  newst = Set.intersection (upReach lv simple) (downReach rt simple')


-- |Cross product of a given sets.
crossProd :: [Set.Set a] -> [[a]]
crossProd [] = []
crossProd (y:ys) = mergeLists y (crossProd ys)


-- |Cross product of a set and the list of tuples.
mergeLists :: Set.Set a -> [[a]] -> [[a]]
mergeLists a [] = [[x] | x <- Set.toList a]
mergeLists a b = [x:y | x <- Set.toList a, y <- b ]
