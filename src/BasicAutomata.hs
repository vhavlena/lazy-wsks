{-|
Module      : BasicAutomata
Description : Basic tree automata used for WS2S decision procedure.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module BasicAutomata where


import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.List as List
import qualified TreeAutomaton as TA
import qualified AuxFunctions as Aux
import qualified Logic as Lo
import qualified Alphabet as Alp
--import BaseDecisionProcedure

import qualified Debug.Trace as Dbg

type State = Int
type WS2STreeAut = TA.BATreeAutomaton State Alp.Symbol

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