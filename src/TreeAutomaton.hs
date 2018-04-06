{-|
Module      : TreeAutomaton
Description : Very basic operations with tree automata (not efficient).
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module TreeAutomaton (
   BATreeAutomaton(..)
   , pre
) where

import qualified Data.Set as Set
import qualified Data.Map as Map


-- |Bottom-up tree automaton
data BATreeAutomaton a b = BATreeAutomaton {
   states :: Set.Set a
   , roots :: Set.Set a
   , leaves :: Set.Set a
   , transitions :: Map.Map ([a],b) (Set.Set a)
} deriving (Show)


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


-- |Cross product of a given sets.
crossProd :: [Set.Set a] -> [[a]]
crossProd [] = []
crossProd (y:ys) = mergeLists y (crossProd ys)


-- |Cross product of a set and the list of tuples.
mergeLists :: Set.Set a -> [[a]] -> [[a]]
mergeLists a [] = [[x] | x <- Set.toList a]
mergeLists a b = [x:y | x <- Set.toList a, y <- b ]
