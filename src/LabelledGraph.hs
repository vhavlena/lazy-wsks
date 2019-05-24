
module LabelledGraph where

import Data.Graph
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Bimap as Bi

type Labeling a = Bi.Bimap Int a
data LabGraph a = LabGraph {
  graph :: Graph
  , label :: Labeling a
}


builLabelGraph :: (Ord a) => [(a,[a])] -> LabGraph a
builLabelGraph lst = LabGraph (buildG (0, Bi.size labMap) edges) labMap where
  labs = List.nub . concat . map (snd)
  labMap = Bi.fromList $ zip [0..] $ labs lst
  edges = lst >>= \(x,y) -> (,) <$> [labMap Bi.!> x] <*> map (labMap Bi.!>) y
