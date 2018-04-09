{-|
Module      : Logic
Description : Basic operations for logic formulae
Author      : Ondrej Lengal, Vojtech Havlena, 2018
License     : GPL-3
-}

module Logic where

import Data.List


-- second-order variable type
type Var = String

-- Atomic formula
data Atom =
   Sing Var
   | Cat Var Var
   | Subseteq Var Var
   | Eps Var


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
showAtom (Cat v1 v2) = v1 ++ "=" ++ v2 ++ ".L"
showAtom (Subseteq v1 v2) = v1 ++ "⊆" ++ v2
showAtom (Eps v) = v ++ "=ε"

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
freeVarsAtom (Cat x y) = [x,y]
freeVarsAtom (Subseteq x y) = [x,y]
freeVarsAtom (Eps x) = [x]


antiprenex :: Formula -> Formula
antiprenex f@(FormulaAtomic _) = f
antiprenex (Disj f1 f2)        = Disj (antiprenex f1) (antiprenex f2)
antiprenex (Conj f1 f2)        = Conj (antiprenex f1) (antiprenex f2)
antiprenex (Neg f)             = Neg (antiprenex f)
antiprenex (Exists var f) =
  case f of
    Disj g1 g2 -> (Exists var $ antiprenex g1) `Disj` (Exists var $ antiprenex g2)
    _          -> Exists var $ antiprenex f
antiprenex (ForAll var f) =
  case f of
    Conj g1 g2 -> (ForAll var $ antiprenex g1) `Conj` (ForAll var $ antiprenex g2)
    _          -> ForAll var $ antiprenex f
