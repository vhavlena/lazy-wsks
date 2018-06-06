{-|
Module      : Logic
Description : Basic operations for logic formulae
Author      : Ondrej Lengal, Vojtech Havlena, 2018
License     : GPL-3
-}

module Logic where

import Data.List
import Data.Monoid
import qualified Data.Foldable as Fd


-- second-order variable type
type Var = String

-- Atomic formula
data Atom =
   Sing Var
   | Cat1 Var Var
   | Cat2 Var Var
   | Subseteq Var Var
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


-- Chain of quantifiers
data QuantifChain a =
  EmptyChain
  | ForAllChain a
  | ExistsChain a


-- Chain of quantifiers with variables
type QuantifVarChain = QuantifChain [Var]


-- |Definition of functor of QuantifChain
instance Functor QuantifChain where
  fmap f EmptyChain = EmptyChain
  fmap f (ExistsChain val) = ExistsChain (f val)
  fmap f (ForAllChain val) = ForAllChain (f val)


-- |Definition of applicative functor of QuantifChain
instance Applicative QuantifChain where
  pure = ExistsChain
  EmptyChain <*> _ = EmptyChain
  (ExistsChain f) <*> st = fmap f st
  (ForAllChain f) <*> st = fmap f st


-- |Definition of Semigroup of QuantifChain
instance (Monoid a) => Semigroup (QuantifChain a) where
  (<>) = mappend


-- |Definition of monoid of QuantifChain
instance (Monoid a) => Monoid (QuantifChain a) where
  mempty = EmptyChain
  mappend EmptyChain s = s
  mappend s EmptyChain = s
  mappend (ForAllChain v1) (ForAllChain v2) = ForAllChain (mappend v1 v2)
  mappend (ExistsChain v1) (ExistsChain v2) = ExistsChain (mappend v1 v2)


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
freeVarsAtom (Eps x) = [x]
freeVarsAtom (Neq x y) = [x,y]
freeVarsAtom (Eqn x y) = [x,y]


-- |Flush (unfold) a chain of existential quantifiers. Given list of variables,
-- it expands to a chain of existential quatifiers, on the most nested level with
-- formula f.
flushQuantifChain :: QuantifVarChain -> Formula -> Formula
flushQuantifChain EmptyChain f = f
flushQuantifChain (ForAllChain xs) f = Fd.foldr (ForAll) f xs
flushQuantifChain (ExistsChain xs) f = Fd.foldr (Exists) f xs


-- |Propagate quantifiers to binary formula operator (conjunction, disjunction).
propagateTo :: (Formula -> Formula -> Formula) -> Formula -> Formula -> QuantifVarChain -> Formula
propagateTo cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVar f1 rem1) (antiprenexFreeVar f2 rem2)) where
  fv1 = fmap (intersect (freeVars f1)) chain
  fv2 = fmap (intersect (freeVars f2)) chain
  remChain = (intersect) <$> fv1 <*> fv2
  rem1 = (\\) <$> fv1 <*> remChain
  rem2 = (\\) <$> fv2 <*> remChain


-- |Antiprenexing  with quantifiers distribution and permutation. Given starting
-- chain of quantifiers.
antiprenexFreeVar :: Formula -> QuantifVarChain -> Formula
antiprenexFreeVar (Neg f) chain = flushQuantifChain chain (Neg $ antiprenexFreeVar f EmptyChain)
antiprenexFreeVar (Conj f1 f2) chain = propagateTo (Conj) f1 f2 chain
antiprenexFreeVar (Disj f1 f2) chain = propagateTo (Disj) f1 f2 chain
antiprenexFreeVar (Exists var f) chain@(ForAllChain c) = flushQuantifChain chain (antiprenexFreeVar f (ExistsChain [var]))
antiprenexFreeVar (Exists var f) EmptyChain = antiprenexFreeVar f ((:) <$> (ExistsChain var) <*> (ExistsChain []))
antiprenexFreeVar (Exists var f) chain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> chain)
antiprenexFreeVar (ForAll var f) chain@(ExistsChain c) = flushQuantifChain chain (antiprenexFreeVar f (ForAllChain [var]))
antiprenexFreeVar (ForAll var f) EmptyChain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> (ForAllChain []))
antiprenexFreeVar (ForAll var f) chain = antiprenexFreeVar f ((:) <$> (ForAllChain var) <*> chain)
antiprenexFreeVar f@(FormulaAtomic _) chain = flushQuantifChain chain f


-- |Antiprenexing.
antiprenex :: Formula -> Formula
antiprenex f = antiprenexFreeVar f EmptyChain


-- |Simplyfication of a given formula.
simplifyFormula :: Formula -> Formula
simplifyFormula = simplifyNeg . moveNegToLeaves . simplifyNeg


-- |Simplification of double negation.
simplifyNeg :: Formula -> Formula
simplifyNeg (Neg (Neg f)) = simplifyNeg f
simplifyNeg f@(FormulaAtomic _) = f
simplifyNeg (Disj f1 f2) = Disj (simplifyNeg f1) (simplifyNeg f2)
simplifyNeg (Conj f1 f2) = Conj (simplifyNeg f1) (simplifyNeg f2)
simplifyNeg (Neg f) = Neg (simplifyNeg f)
simplifyNeg (ForAll var f) = ForAll var (simplifyNeg f)
simplifyNeg (Exists var f) = Exists var (simplifyNeg f)


-- |Move negation to the formula leaves.
moveNegToLeaves :: Formula -> Formula
moveNegToLeaves (Neg (Conj f1 f2)) = moveNegToLeaves (Disj (Neg f1) (Neg f2))
moveNegToLeaves (Neg (Disj f1 f2)) = moveNegToLeaves (Conj (Neg f1) (Neg f2))
moveNegToLeaves (Disj f1 f2) = Disj (moveNegToLeaves f1) (moveNegToLeaves f2)
moveNegToLeaves (Conj f1 f2) = Conj (moveNegToLeaves f1) (moveNegToLeaves f2)
moveNegToLeaves (Neg f) = Neg (moveNegToLeaves f)
moveNegToLeaves (ForAll var f) = ForAll var (moveNegToLeaves f)
moveNegToLeaves (Exists var f) = Exists var (moveNegToLeaves f)
moveNegToLeaves f@(FormulaAtomic _) = f


--getConjunctionList :: Formula -> [Formula]
