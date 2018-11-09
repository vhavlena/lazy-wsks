{-|
Module      : AuxFunctions
Description : Auxiliary functions.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module AuxFunctions (
   insertAt
   , deleteAt
   , prArr
   , crossProd
) where


import Data.List
import qualified Data.Set as Set

-- |Insert a value into list to a given position (indices start at 0).
insertAt :: a -> [a] -> Int -> [a]
insertAt v xs 0 = v : xs
insertAt v (x:xs) n = x : (insertAt v xs (n - 1))


-- |Insert a value from list based on a given position (indices start at 0).
deleteAt :: [a] -> Int -> [a]
deleteAt [] _ = []
deleteAt (x:xs) i
   | i == 0 = xs
   | otherwise = x : deleteAt xs (i-1)


-- |Print list (items are separated by delim).
prArr :: (Show a) => String -> [a] -> String
prArr delim arr = intercalate delim (map (show) arr)


-- |Cross product of a given sets.
crossProd :: [Set.Set a] -> [[a]]
crossProd [] = []
crossProd (y:ys) = mergeLists y (crossProd ys)


-- |Cross product of a set and the list of tuples.
mergeLists :: Set.Set a -> [[a]] -> [[a]]
mergeLists a [] = [[x] | x <- Set.toList a]
mergeLists a b = [x:y | x <- Set.toList a, y <- b ]
