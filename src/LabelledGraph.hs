
module LabelledGraph where

import Data.Graph
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Bimap as Bi

type Labeling a = Bi.Bimap Int a
data LabGraph a = LabGraph {
  graph :: Graph
  , label :: Labeling a
} deriving (Show)


builLabelGraph :: (Ord a) => [(a,[a])] -> LabGraph a
builLabelGraph lst = LabGraph (buildG (0, (Bi.size labMap) - 1) edges) labMap where
  labs x = List.nub $ (concat $ map (snd) x) ++ (map (fst) x)
  labMap = Bi.fromList $ zip [0..] $ labs lst
  edges = lst >>= \(x,y) -> (,) <$> [labMap Bi.!> x] <*> map (labMap Bi.!>) y


reachableLabelGraph :: (Ord a) => a -> LabGraph a -> [a]
reachableLabelGraph ver (LabGraph gph lbl) = map (lbl Bi.!) $ reachable gph (lbl Bi.!> ver)
