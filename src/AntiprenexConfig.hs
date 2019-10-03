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
distrSteps = 4 :: Int

-- |Distributivity configuration (force -- do distribution whenever it is
-- possible, conservative -- only if there is a possibility to move ex.
-- quantifier inside)
distrConfig = DistrForce

-- |Number of chunks for splitting in informed balancing
balInforSplitChunks = 5 :: Int
