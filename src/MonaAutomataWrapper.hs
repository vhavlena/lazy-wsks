{-|
Module      : MonaAutomataWrapper
Description : Mona automata wrapper
Author      : Vojtech Havlena, August 2018
License     : GPL-3
-}

module MonaAutomataWrapper where

import MonaAutomataParser
import TreeAutomaton
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Alphabet as Alp

monaGTAToTA :: MonaGTA -> BATreeAutomaton MonaState Alp.Symbol
monaGTAToTA (MonaGTA header (MonaGuide guide) spaces) = BATreeAutomaton states roots leaves trans where
  guide' = Map.fromList $ map (\(MonaGuideRule _ fr dest) -> (fr, dest)) guide
  vars = variables header
  expSpaces = expandTrans vars spaces
  sizes = getSizes expSpaces
  sizedict = getSizesDict expSpaces sizes
  trans = unifyTransitions vars guide' sizedict expSpaces
  states = Set.fromList [0..(last sizes)-1]
  leaves = Set.fromList $ zipWith (+) sizes $ map (initial) expSpaces
  roots = Set.fromList $ accept header


getSizesDict :: [MonaStateSpace] -> [Int] -> Map.Map Int Int
getSizesDict spaces arr = Map.fromList dict where
  dict = zipWith (\a b -> (iden a,b)) spaces arr


getSizes :: [MonaStateSpace] -> [Int]
getSizes spaces = init . scanl (+) 0 $ map (size) spaces


unifyTransitions :: [Alp.Variable] -> Map.Map MonaState [MonaState] -> Map.Map Int Int -> [MonaStateSpace] -> Map.Map ([MonaState],Alp.Symbol) (Set.Set MonaState)
unifyTransitions vars guide sizes spaces = Map.fromListWith (Set.union) $ foldr1 (++) $ map (unifyStateSpace vars guide sizes) spaces


unifyStateSpace :: [Alp.Variable] -> Map.Map MonaState [MonaState] -> Map.Map Int Int -> MonaStateSpace  -> [(([MonaState],Alp.Symbol), Set.Set MonaState)]
unifyStateSpace vars guide sizes (MonaStateSpace iden _ _ initial trans) = map (conv) trans where
  conv (MonaTransition src sym dest) = ((src', convToSymbol vars sym), Set.singleton dest) where
    pl = Map.findWithDefault [] dest guide
    sizes' = map (\a -> Map.findWithDefault 0 a sizes) pl
    src' = zipWith (+) src sizes'


expandTrans :: [Alp.Variable] -> [MonaStateSpace] -> [MonaStateSpace]
expandTrans vars = map (conv) where
  conv (MonaStateSpace i n s ini tr) = MonaStateSpace i n s ini (tr >>= expandSymbols vars)


expandSymbols :: [Alp.Variable] -> MonaTransition -> [MonaTransition]
expandSymbols vars (MonaTransition src sym dest) = map (\s -> MonaTransition src s dest) expX where
  expX = expandX $ reorderMonaSymbol vars sym


expandX :: String -> [String]
expandX str = listProd (reverse $ str >>= gen) [[]] where
  gen a = if a == 'X' then return ['0','1']
         else return [a]


convToSymbol :: [Alp.Variable] -> String -> Alp.Symbol
convToSymbol vars sym = (sym, Set.fromList vars)


reorderMonaSymbol :: [Alp.Variable] -> String -> String
reorderMonaSymbol vars sym = sym' where
  pair = zip vars sym
  sym' = map (snd) $ sortBy (\x y -> compare (fst x) (fst y)) pair


listProd [] a = a
listProd (x:xs) a = listProd xs (x >>= \b -> map (b:) a)


convertGTA filename = do
  monagta <- parseFile filename
  putStrLn $ show $ monaGTAToTA monagta
