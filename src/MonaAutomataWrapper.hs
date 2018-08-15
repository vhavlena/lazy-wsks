{-|
Module      : MonaAutomataWrapper
Description : Mona automata wrapper
Author      : Vojtech Havlena, August 2018
License     : GPL-3
-}

module MonaAutomataWrapper where

import MonaAutomataParser
import TreeAutomaton
import qualified Data.Map as Map
import qualified Alphabet as Alp

monaGTAToTA :: MonaGTA -> BATreeAutomaton MonaState String
monaGTAToTA (MonaGTA header guide spaces) =  where
  guide' = Map.fromList $ map (\(MonaGuideRule _ fr dest) -> (fr, dest)) guide
  sizes = getSizes spaces
  trans = unifyTransitions guide' sizes spaces
  states = [0..(last sizes)-1]


getSizes :: [MonaStateSpace] -> Map.Map Int Int
getSizes spaces = Map.fromList dict where
  arr = init . scanl (+) 0 $ map (size) spaces
  dict = zipWith (\a b -> (iden a,b)) spaces arr


unifyTransitions :: Map.Map MonaState [MonaState] -> Map.Map Int Int -> [MonaStateSpace] -> Map.Map ([a],b) (Set.Set a)
unifyTransitions guide sizes spaces = Map.fromList $ foldr1 (++) $ map (unifyStateSpace guide sizes) spaces


unifyStateSpace :: Map.Map MonaState [MonaState] -> Map.Map Int Int -> MonaStateSpace  -> [(([a],b),a)]
unifyStateSpace guide sizes (MonaStateSpace iden _ _ initial trans) = map (conv) trans where
  conv (MonaTransition src sym dest) = ((src',sym),dest) where
    pl = Map.findWithDefault 0 dest guide
    sizes' = map (\a -> Map.findWithDefault 0 a sizes) pl
    src' = zipWith (+) src sizes'
