{-|
Module      : Logic
Description : Basic operations for logic formulae
Author      : Ondrej Lengal, Vojtech Havlena, 2018
License     : GPL-3
-}

module Logic where

import Data.List
import Data.Monoid


-- second-order variable type
type Var = String

-- Atomic formula
data Atom =
   Sing Var
   | Cat1 Var Var
   | Cat2 Var Var
   | Subseteq Var Var
   | Subset Var Var
   | In Var Var
   | Eps Var
   | Neq Var Var
   | Eqn Var Var


-- formula type
data Formula =
  FormulaAtomic Atom
  | Disj Formula Formula
  | Conj Formula Formula
  | Neg Formula
  | Exists Var Formula
  | ForAll Var Formula


-- prints the formula in human-readable format
showFormula :: Formula -> String
showFormula (FormulaAtomic phi) = show phi
showFormula (Disj f1 f2)        = "(" ++ (showFormula f1) ++ ") ∨ (" ++ (showFormula f2) ++ ")"
showFormula (Conj f1 f2)        = "(" ++ (showFormula f1) ++ ") ∧ (" ++ (showFormula f2) ++ ")"
showFormula (Neg f)             = "¬(" ++ (showFormula f) ++ ")"
showFormula (Exists var f)      = "∃" ++ var ++ ". (" ++ (showFormula f) ++ ")"
showFormula (ForAll var f)      = "∀" ++ var ++ ". (" ++ (showFormula f) ++ ")"

-- |Print atom in human-readable format
showAtom :: Atom -> String
showAtom (Sing v) = "Sing(" ++ v ++ ")"
showAtom (Cat1 v1 v2) = v1 ++ "=" ++ v2 ++ ".L"
showAtom (Subseteq v1 v2) = v1 ++ "⊆" ++ v2
showAtom (Eps v) = v ++ "=ε"
showAtom (Neq v1 v2) = v1 ++ "~=" ++ v2
showAtom (Eqn v1 v2) = v1 ++ "=" ++ v2
showAtom (In v1 v2) = v1 ++ " in " ++ v2
showAtom (Subset v1 v2) = v1 ++ "⊂" ++ v2

-- instantiance of the data type as class Show
instance Show Formula where
  show = showFormula


-- |For converting atom to string
instance Show Atom where
   show = showAtom


-- removes the universal quantifier
removeForAll :: Formula -> Formula
removeForAll (FormulaAtomic phi) = (FormulaAtomic phi)
removeForAll (Disj f1 f2)        = (Disj (removeForAll f1) (removeForAll f2))
removeForAll (Conj f1 f2)        = (Conj (removeForAll f1) (removeForAll f2))
removeForAll (Neg f)             = (Neg (removeForAll f))
removeForAll (Exists var f)      = (Exists var (removeForAll f))
removeForAll (ForAll var f)      = (Neg $ Exists var $ Neg (removeForAll f))


-- |Replace atoms which are not basic.
removeAtoms :: Formula -> Formula
removeAtoms (FormulaAtomic (Neq v1 v2)) = Neg (FormulaAtomic (Eqn v1 v2))
removeAtoms (FormulaAtomic phi) = (FormulaAtomic phi)
removeAtoms (Disj f1 f2)        = (Disj (removeAtoms f1) (removeAtoms f2))
removeAtoms (Conj f1 f2)        = (Conj (removeAtoms f1) (removeAtoms f2))
removeAtoms (Neg f)             = (Neg (removeAtoms f))
removeAtoms (Exists var f)      = (Exists var (removeAtoms f))
removeAtoms (ForAll var f)      = (Neg $ Exists var $ Neg (removeAtoms f))


-- |Convert to base formula containing only basic atoms and quantifiers.
convertToBaseFormula :: Formula -> Formula
convertToBaseFormula = removeAtoms . removeForAll


-- retrieves free variables of a formula
freeVars :: Formula -> [Var]
freeVars (FormulaAtomic phi) = freeVarsAtom phi
freeVars (Disj f1 f2)   = nub $ (freeVars f1) ++ (freeVars f2)
freeVars (Conj f1 f2)   = freeVars (Disj f1 f2)
freeVars (Neg f)        = freeVars f
freeVars (Exists var f) = delete var $ freeVars f
freeVars (ForAll var f) = freeVars (Exists var f)


-- |Free variables in atoms.
freeVarsAtom :: Atom -> [Var]
freeVarsAtom (Sing x) = [x]
freeVarsAtom (Cat1 x y) = [x,y]
freeVarsAtom (Subseteq x y) = [x,y]
freeVarsAtom (Subset x y) = [x,y]
freeVarsAtom (Eps x) = [x]
freeVarsAtom (Neq x y) = [x,y]
freeVarsAtom (Eqn x y) = [x,y]
freeVarsAtom (In x y) = [x,y]
