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
  | BalFullTree
  deriving (Eq)

-- |Rename bound vars.
renameBoundVars = True

-- |Formula balancing (conjunction and disjunction)
balanceFormulaConfig = BalInformed

-- |Number of distribution steps
distrSteps = 2 :: Int
