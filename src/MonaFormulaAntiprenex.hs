{-|
Module      : MonaFormulaAntiprenex
Description : Mona formulae antiprenexing
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaFormulaAntiprenex where


import Data.List
import Data.Maybe

import MonaParser
import MonaFormulaOperation

import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with antiprenexing
--------------------------------------------------------------------------------------------------------------

-- Chain of quantifiers
data QuantifChain a =
  ForAll0Chain a
  | ForAll1Chain a
  | ForAll2Chain a
  | Exists0Chain a
  | Exists1Chain a
  | Exists2Chain a
  deriving (Eq)


-- Chain of quantifiers with variables
type QuantifVarChain = QuantifChain (String, Maybe MonaFormula)



-- |Flush (unfold) a chain of existential quantifiers. Given list of variables,
-- it expands to a chain of existential quatifiers, on the most nested level with
-- formula f.
flushQuantifChain :: [QuantifVarChain] -> MonaFormula -> MonaFormula
flushQuantifChain [] f = f
flushQuantifChain ((ForAll0Chain x):xs) f = MonaFormulaAll0 [fst x] (flushQuantifChain xs f)
flushQuantifChain ((ForAll1Chain x):xs) f = MonaFormulaAll1 [x] (flushQuantifChain xs f)
flushQuantifChain ((ForAll2Chain x):xs) f = MonaFormulaAll2 [x] (flushQuantifChain xs f)
flushQuantifChain ((Exists0Chain x):xs) f = MonaFormulaEx0 [fst x] (flushQuantifChain xs f)
flushQuantifChain ((Exists1Chain x):xs) f = MonaFormulaEx1 [x] (flushQuantifChain xs f)
flushQuantifChain ((Exists2Chain x):xs) f = MonaFormulaEx2 [x] (flushQuantifChain xs f)


getChainVarName :: QuantifVarChain -> String
getChainVarName (ForAll0Chain a) = fst a
getChainVarName (ForAll1Chain a) = fst a
getChainVarName (ForAll2Chain a) = fst a
getChainVarName (Exists0Chain a) = fst a
getChainVarName (Exists1Chain a) = fst a
getChainVarName (Exists2Chain a) = fst a


-- |Propagate quantifiers to binary formula operator (conjunction, disjunction).
propagateTo :: (MonaFormula -> MonaFormula -> MonaFormula) -> MonaFormula -> MonaFormula -> [QuantifVarChain] -> MonaFormula
propagateTo cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVar f1 rem1) (antiprenexFreeVar f2 rem2)) where
  vars1 = freeVarsFormula f1
  vars2 = freeVarsFormula f2
  fv1 = filter (\a -> elem (getChainVarName a) vars1) chain
  fv2 = filter (\a -> elem (getChainVarName a) vars2) chain
  remChain = intersect fv1 fv2
  rem1 = fv1 \\ remChain
  rem2 = fv2 \\ remChain


-- |Antiprenexing  with quantifiers distribution and permutation. Given starting
-- chain of quantifiers.
antiprenexFreeVar :: MonaFormula -> [QuantifVarChain] -> MonaFormula
antiprenexFreeVar (MonaFormulaNeg f) chain = flushQuantifChain chain (MonaFormulaNeg $ antiprenexFreeVar f [])
antiprenexFreeVar (MonaFormulaConj f1 f2) chain = propagateTo (MonaFormulaConj) f1 f2 chain
antiprenexFreeVar (MonaFormulaDisj f1 f2) chain = propagateTo (MonaFormulaDisj) f1 f2 chain
antiprenexFreeVar (MonaFormulaEx0 [var] f) chain = antiprenexFreeVar f ((Exists0Chain (var, Nothing)):chain)
antiprenexFreeVar (MonaFormulaEx1 [var] f) chain = antiprenexFreeVar f ((Exists1Chain var):chain)
antiprenexFreeVar (MonaFormulaEx2 [var] f) chain = antiprenexFreeVar f ((Exists2Chain var):chain)
antiprenexFreeVar (MonaFormulaAll0 [var] f) chain = antiprenexFreeVar f ((ForAll0Chain (var, Nothing)):chain)
antiprenexFreeVar (MonaFormulaAll1 [var] f) chain = antiprenexFreeVar f ((ForAll1Chain var):chain)
antiprenexFreeVar (MonaFormulaAll2 [var] f) chain = antiprenexFreeVar f ((ForAll2Chain var):chain)
antiprenexFreeVar atom@(MonaFormulaAtomic _) chain = flushQuantifChain chain atom
antiprenexFreeVar a _ = error $ "antiprenexFreeVar: not supported" ++ (show a)


antiprenexFormula :: MonaFormula -> MonaFormula
antiprenexFormula f = simplifyNegFormula $ antiprenexFreeVar ( moveNegToLeavesFormula $ convertToBaseFormula f) []


antiprenexDecl :: MonaDeclaration -> MonaDeclaration
antiprenexDecl (MonaDeclFormula f) = MonaDeclFormula $ antiprenexFormula f
antiprenexDecl (MonaDeclVar1 [(var, decl)]) = MonaDeclVar1 [(var,decl >>= return . antiprenexFormula)]
antiprenexDecl (MonaDeclVar2 [(var, decl)]) = MonaDeclVar2 [(var,decl >>= return . antiprenexFormula)]
antiprenexDecl (MonaDeclPred name params f) = MonaDeclPred name params (antiprenexFormula f) -- TODO: params are not antiprenexed
antiprenexDecl a = a -- TODO: incomplete


antiprenexFile :: MonaFile -> MonaFile
antiprenexFile (MonaFile dom decls) = MonaFile dom $ map (antiprenexDecl) decls


convertToBaseFormula :: MonaFormula -> MonaFormula
convertToBaseFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
convertToBaseFormula (MonaFormulaVar var) = MonaFormulaVar var
convertToBaseFormula (MonaFormulaNeg f) = MonaFormulaNeg (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaImpl f1 f2) = MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaEquiv f1 f2) = MonaFormulaConj (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)) (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f2) (convertToBaseFormula f1))
convertToBaseFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (convertToBaseFormula f)


moveNegToLeavesFormula :: MonaFormula -> MonaFormula
moveNegToLeavesFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
moveNegToLeavesFormula (MonaFormulaVar var) = MonaFormulaVar var
moveNegToLeavesFormula (MonaFormulaNeg (MonaFormulaConj f1 f2)) = moveNegToLeavesFormula $ MonaFormulaDisj (MonaFormulaNeg f1) (MonaFormulaNeg f2)
moveNegToLeavesFormula (MonaFormulaNeg (MonaFormulaDisj f1 f2)) = moveNegToLeavesFormula $ MonaFormulaConj (MonaFormulaNeg f1) (MonaFormulaNeg f2)
moveNegToLeavesFormula (MonaFormulaNeg f) = MonaFormulaNeg (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (moveNegToLeavesFormula f1) (moveNegToLeavesFormula f2)
moveNegToLeavesFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (moveNegToLeavesFormula f1) (moveNegToLeavesFormula f2)
moveNegToLeavesFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (moveNegToLeavesFormula f)
moveNegToLeavesFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (moveNegToLeavesFormula f)


simplifyNegFormula :: MonaFormula -> MonaFormula
simplifyNegFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
simplifyNegFormula (MonaFormulaVar var) = MonaFormulaVar var
simplifyNegFormula (MonaFormulaNeg (MonaFormulaNeg f)) = simplifyNegFormula f
simplifyNegFormula (MonaFormulaNeg f) = MonaFormulaNeg (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (simplifyNegFormula f)
