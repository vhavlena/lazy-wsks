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
   , simplifyTrans
   , reverseSimplified
   , backReach
   , toSingleton
) where

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified AuxFunctions as Aux
import qualified Alphabet as Alp

-- |Type for single transition and a transition function
type Transitions a b = Map.Map ([a],b) (Set.Set a)
type Transition a b = (([a],b), Set.Set a)
type SimplTransition a = (a,a)
--type SimplTransitionRev a = (a,a)

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


simplifyTrans :: [Transition a b] -> [SimplTransition a]
simplifyTrans trans = trans >>= \((x,_),y) -> Set.toList y >>= \z -> x >>= \b -> return (b,z)


reverseSimplified :: [SimplTransition a] -> [SimplTransition a]
reverseSimplified = map (\(x,y) -> (y,x))

backReachStep :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
backReachStep states trans = Set.fromList $ ((Set.toList states) >>= \x -> (Set.toList $ Map.findWithDefault Set.empty x trans) )


backReach :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
backReach states trans = if Set.isSubsetOf states' states then states else backReach (Set.union states states') trans where
  states' = backReachStep states trans


toSingleton :: [(a,b)] -> [(a,Set.Set b)]
toSingleton = map (\(x,y) -> (x, Set.singleton y))


-- |Cross product of a given sets.
crossProd :: [Set.Set a] -> [[a]]
crossProd [] = []
crossProd (y:ys) = mergeLists y (crossProd ys)


-- |Cross product of a set and the list of tuples.
mergeLists :: Set.Set a -> [[a]] -> [[a]]
mergeLists a [] = [[x] | x <- Set.toList a]
mergeLists a b = [x:y | x <- Set.toList a, y <- b ]
