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
) where


import Data.List

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


prArr :: (Show a) => String -> [a] -> String
prArr delim arr = intercalate delim (map (show) arr)
