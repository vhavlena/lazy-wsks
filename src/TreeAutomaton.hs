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
   , preCom
   , ComState(..)
   , ComTA(..)
   , containsRoot
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


data ComState a =
  Sink
  | State a
  | ConjSt (ComState a) (ComState a)
  | DisjSt (ComState a) (ComState a)
  deriving (Eq, Ord)


data ComTA a b =
  Base (BATreeAutomaton a b) [Alp.Variable]
  | ConjTA (ComTA a b) (ComTA a b)
  | DisjTA (ComTA a b) (ComTA a b)
  deriving (Eq, Ord)


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


instance (Show a) => Show (ComState a) where
  show Sink = "#"
  show (State s) = show s
  show (ConjSt s1 s2) = show s1 ++ "&" ++ show s2
  show (DisjSt s1 s2) = show s1 ++ "+" ++ show s2


instance (Show a, Show b) => Show (ComTA a b) where
  show (Base a _) = show a
  show (ConjTA a1 a2) = show a1 ++ "&" ++ show a2
  show (DisjTA a1 a2) = show a1 ++ "+" ++ show a2

-- -- |Pre (Up) of a set of states wrt given symbol.
-- pre :: (Ord a, Ord b) => BATreeAutomaton a b -> [Set.Set a] -> b -> Set.Set a
-- pre (BATreeAutomaton _ _ _ tr) st sym =
--   if Set.null cons then cons
--   else cons
--   where
--    cons = foldr (Set.union) Set.empty [Map.findWithDefault Set.empty (s,sym) tr | s <- crossProd st ]


-- |Pre (Up) of a set of states wrt given symbol.
pre :: (Ord a, Ord b) => ([Alp.Variable] -> b -> b) -> ComTA a b -> [Set.Set (ComState a)] -> b -> Set.Set (ComState a)
pre proj aut st sym =
  foldr (Set.union) Set.empty [preCom proj aut s1 s2 sym | [s1, s2] <- crossProd st ]



-- |Pre (Up) of a set of states wrt given symbol.
preCom :: (Ord a, Ord b) => ([Alp.Variable] -> b -> b) -> ComTA a b -> ComState a -> ComState a -> b -> Set.Set (ComState a)
preCom proj (ConjTA aut1 aut2) (ConjSt s1 s2) (ConjSt u1 u2) sym = Set.fromList [ConjSt a b | a <- a1, b <- a2]
  where
    a1 = Set.toList $ preCom proj aut1 s1 u1 sym
    a2 = Set.toList $ preCom proj aut2 s2 u2 sym
preCom proj (DisjTA aut1 aut2) (DisjSt s1 s2) (DisjSt u1 u2) sym = Set.fromList [DisjSt a b | a <- a1, b <- a2]
  where
    a1 = Set.toList $ preCom proj aut1 s1 u1 sym
    a2 = Set.toList $ preCom proj aut2 s2 u2 sym
preCom _ _ (State q) Sink _ = Set.singleton Sink
preCom _ _ Sink (State q) _ = Set.singleton Sink
preCom _ _ Sink Sink _ = Set.singleton Sink
preCom proj (Base (BATreeAutomaton _ _ _ tr) vars) (State q) (State r) sym =
    if null step then Set.singleton Sink
    else Set.map (State) step where
      step = Map.findWithDefault (Set.empty) ([q,r], (proj vars sym)) tr


isRoot :: (Ord a, Ord b) => ComTA a b -> ComState a -> Bool
isRoot _ Sink = False
isRoot (Base aut _) (State st) = Set.member st (roots aut)
isRoot (ConjTA aut1 aut2) (ConjSt st1 st2) = (isRoot aut1 st1) && (isRoot aut2 st2)
isRoot (DisjTA aut1 aut2) (DisjSt st1 st2) = (isRoot aut1 st1) || (isRoot aut2 st2)

containsRoot :: (Ord a, Ord b) => ComTA a b -> Set.Set (ComState a) -> Bool
containsRoot aut st = any (isRoot aut) (Set.toList st)


-- |Simplify TA transitions (remove symbol, break a set of the destination
-- states into transitions with a single destination state).
simplifyTrans :: (Ord a) => [Transition a b] -> [SimplTransition a]
simplifyTrans trans = Set.toList $ Set.fromList (trans >>= transform) where
  transform ((x,_),y) = Set.toList y >>= \z -> return (x,z)


-- |Reverse the direction of simplified transitions.
reverseSimplified :: [SimplTransition a] -> [SimplTransitionRev a]
reverseSimplified tr = tr >>= \(x,y) -> x >>= \z -> return (y,z)


-- |Downward reachability step (in the reverse direction of TA transitions). The
-- function uses simplified transitions (without symbols).
downReachStep :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
downReachStep states trans = Set.fromList $ ((Set.toList states) >>= choose) where
  choose x = Set.toList $ Map.findWithDefault Set.empty x trans


-- |Downward reachability (reachability from the root states, in the reverse
-- direction of TA transtions). Graph reachability is performed (i.e, regardless
-- the transition symbols). The function uses simplified transitions (without symbols).
downReach :: (Ord a) => Set.Set a -> Map.Map a (Set.Set a) -> Set.Set a
downReach states trans =
  if Set.isSubsetOf states' states then states
  else downReach (Set.union states states') trans where
    states' = downReachStep states trans


-- |Upward reachability step (in the direction of TA transitions). The function
-- uses simplified transitions (without symbols).
upReachStep :: (Ord a) => Set.Set a -> [SimplTransition a] -> Set.Set a
upReachStep states trans = Set.fromList $ (trans >>= choose) where
  choose (x,y) = if Set.isSubsetOf (Set.fromList x) states then return y else []


-- |Upward reachability (reachability from the leaf states, in the direction of
-- TA transtions). Graph reachability is performed (i.e, regardless the transition
-- symbols). The function uses simplified transitions (without symbols).
upReach :: (Ord a) => Set.Set a -> [SimplTransition a] -> Set.Set a
upReach states trans =
  if Set.isSubsetOf states' states then states
  else upReach (Set.union states states') trans where
    states' = upReachStep states trans


-- |Remove transitions whose corresponding states are not in a given set of states.
transProj :: (Ord a) => Set.Set a -> [Transition a b] -> [Transition a b]
transProj states trans = filter (proj) $ map (select) trans where
  proj ((x,_),y) = (Set.isSubsetOf (Set.fromList x) states) && (not $ Set.null y)
  select t@((x,s),y) = ((x,s),Set.intersection y states)


-- |Restriction of a given automaton to a given set of states
autRestriction :: (Ord a, Ord b) => Set.Set a -> BATreeAutomaton a b -> BATreeAutomaton a b
autRestriction states (BATreeAutomaton st rt lv tr) = BATreeAutomaton newst newrt newlv newtr where
  newrt = Set.intersection states rt
  newlv = Set.intersection states lv
  newst = Set.intersection states st
  newtr = Map.fromList $ transProj states (Map.toList tr)


-- |Remove nonaccessible and noncoaccessible states from automaton (states that
-- are not reachable from the root states and from the leaf states).
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


-- |Convert a list of pairs to a list of pairs whose second item
-- is a singleton set.
toSingleton :: [(a,b)] -> [(a,Set.Set b)]
toSingleton = map (\(x,y) -> (x, Set.singleton y))
