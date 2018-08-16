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
import qualified Data.Set as Set
import qualified Alphabet as Alp

monaGTAToTA :: MonaGTA -> BATreeAutomaton MonaState String
monaGTAToTA (MonaGTA header (MonaGuide guide) spaces) = BATreeAutomaton states roots leaves trans where
  guide' = Map.fromList $ map (\(MonaGuideRule _ fr dest) -> (fr, dest)) guide
  sizes = getSizes spaces
  sizedict = getSizesDict spaces sizes
  trans = unifyTransitions guide' sizedict spaces
  states = Set.fromList [0..(last sizes)-1]
  leaves = Set.fromList $ zipWith (+) sizes $ map (initial) spaces
  roots = Set.fromList $ accept header


getSizesDict :: [MonaStateSpace] -> [Int] -> Map.Map Int Int
getSizesDict spaces arr = Map.fromList dict where
  dict = zipWith (\a b -> (iden a,b)) spaces arr


getSizes :: [MonaStateSpace] -> [Int]
getSizes spaces = init . scanl (+) 0 $ map (size) spaces


unifyTransitions ::  Map.Map MonaState [MonaState] -> Map.Map Int Int -> [MonaStateSpace] -> Map.Map ([MonaState],MonaSymbol) (Set.Set MonaState)
unifyTransitions guide sizes spaces = Map.fromListWith (Set.union) $ foldr1 (++) $ map (unifyStateSpace guide sizes) spaces


unifyStateSpace :: Map.Map MonaState [MonaState] -> Map.Map Int Int -> MonaStateSpace  -> [(([MonaState],MonaSymbol), Set.Set MonaState)]
unifyStateSpace guide sizes (MonaStateSpace iden _ _ initial trans) = map (conv) trans where
  conv (MonaTransition src sym dest) = ((src',sym), Set.singleton dest) where
    pl = Map.findWithDefault [] dest guide
    sizes' = map (\a -> Map.findWithDefault 0 a sizes) pl
    src' = zipWith (+) src sizes'


convertGTA filename = do
  monagta <- parseFile filename
  putStrLn $ show $ monaGTAToTA monagta
