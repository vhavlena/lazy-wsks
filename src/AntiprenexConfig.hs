{-|
Module      : AntiprenexConfig
Description : Antiprenex config file
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module AntiprenexConfig where


-- |Formula balancing alternatives
data BalanceFormulaConfig =
  BalInformed
  | BalInformedSplit
  | BalFullTree
  deriving (Eq)

data DistributionConfig =
  DistrConservative
  | DistrForce
  deriving (Eq)

-- |Rename bound vars.
renameBoundVars = True

-- |Formula balancing (conjunction and disjunction)
balanceFormulaConfig = BalInformedSplit

-- |Number of distribution steps
distrSteps = 3 :: Int

-- |Threshold for total number of states for distributivity
distrThreshold = 10000 :: Integer

-- |Threshold of subformulas for the balancing prefix
prefSubformulaCount = 300 :: Int
-- |Threshold of subformulas for antiprenexing
antiprenexSubformulaCount = 10000 :: Int

-- |Distributivity configuration (force -- do distribution whenever it is
-- possible, conservative -- only if there is a possibility to move ex.
-- quantifier inside)
distrConfig = DistrConservative

-- |Number of chunks for splitting in informed balancing
balInforSplitChunks = 5 :: Int

balInforSplitHigh = 10 :: Int
