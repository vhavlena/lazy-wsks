{-|
Module      : ProcedureCheck
Description : Functions for checking wheather logic is appropriate fragment.
Author      : Vojtech Havlena, 2020
License     : GPL-3
-}

module ProcedureCheck where

import qualified Logic as Lo
import qualified Data.Map as Map
import qualified BaseDecisionProcedure as BD

-- |Check whether atoms are supported in our fragment
isAtomSup :: BD.MonaAutDict -> Lo.Atom -> Either String Bool
isAtomSup autdict (Lo.MonaAt at _) = case (Map.lookup (show at) autdict) of
  Just aut -> Right True
  Nothing -> Left $ show at
isAtomSup _ _ = Right True


-- |Is formula supported in the lazy decision procedure
isFormulaSup :: BD.MonaAutDict -> Lo.Formula -> Either String Bool
isFormulaSup autdict (Lo.FormulaAtomic atom) = isAtomSup autdict atom
isFormulaSup autdict (Lo.Disj f1 f2) = (isFormulaSup autdict f1) >> (isFormulaSup autdict f2)
isFormulaSup autdict (Lo.Conj f1 f2) = (isFormulaSup autdict f1) >> (isFormulaSup autdict f2)
isFormulaSup autdict (Lo.Neg f) = isFormulaSup autdict f
isFormulaSup autdict (Lo.Exists var f) = isFormulaSup autdict f
isFormulaSup _ (Lo.ForAll _ _) = Left "Forall"
