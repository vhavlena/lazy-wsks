{-|
Module      : MonaFormulaAntiprenex
Description : Mona formulae antiprenexing
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaFormulaAntiprenex where


import Data.List
import Data.Maybe

import AntiprenexConfig
import MonaFormula
import MonaFormulaOperation
import MonaFormulaOperationSubst
import MonaFormulaBalance
import MonaFormulaDistr
import MonaFormulaInfo

import qualified Relation as Rel
import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as Lst
import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with informed antiprenexing
--------------------------------------------------------------------------------------------------------------

-- |Propagate quantifiers to binary formula operator (conjunction, disjunction).
propagateTo ::
  FormulaFV
  -> (MonaFormula -> MonaFormula -> MonaFormula)
  -> MonaFormula
  -> MonaFormula
  -> [QuantifVarChain]
  -> MonaFormula
propagateTo fv cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVar fv f1 rem1) (antiprenexFreeVar fv f2 rem2)) where --TODO: ex1 x where ..., y where ..., --> does not consider free variables in where declaration
  vars1 = freeVarsFormula f1
  vars2 = freeVarsFormula f2
  fv1 = filter (\a -> elem (getChainVarName a) vars1) chain
  fv2 = filter (\a -> elem (getChainVarName a) vars2) chain
  remChain = reverse $ intersect fv1 fv2
  rem1 = fv1 \\ remChain
  rem2 = fv2 \\ remChain


-- |Antiprenexing  with quantifiers distribution and permutation. Given starting
-- chain of quantifiers.
antiprenexFreeVar :: FormulaFV -> MonaFormula -> [QuantifVarChain] -> MonaFormula
antiprenexFreeVar fv (MonaFormulaNeg f) chain = flushQuantifChain chain (MonaFormulaNeg $ antiprenexFreeVar fv f [])
--antiprenexFreeVar (MonaFormulaConj f1 f2) chain = propagateTo (MonaFormulaConj) f1 f2 chain
antiprenexFreeVar fv f@(MonaFormulaConj f1 f2) chain = case balanceFormulaConfig of
  BalInformed -> balanceFormulaInf fv (antiprenexFreeVar fv) f $ chain
  BalInformedSplit -> if (length $ getConjList f) >= 5 then propagateTo fv (MonaFormulaConj) f1 f2 chain else balanceFormulaInfSplit fv (antiprenexFreeVar fv) f $ chain
  BalFullTree -> propagateTo fv (MonaFormulaConj) f1 f2 chain
antiprenexFreeVar fv (MonaFormulaDisj f1 f2) chain = MonaFormulaDisj (antiprenexFreeVar fv f1 chain) (antiprenexFreeVar fv f2 chain) -- propagateTo (MonaFormulaDisj) f1 f2 chain
antiprenexFreeVar fv (MonaFormulaEx0 [var] f) chain = MonaFormulaEx0 [var] (antiprenexFreeVar (fvUpdateLocal fv var 0) f chain) --antiprenexFreeVar f ((Exists0Chain (var, Nothing)):chain)
antiprenexFreeVar fv (MonaFormulaEx1 [var] f) chain = antiprenexFreeVar (fvUpdateLocal fv (fst var) 1) f ((Exists1Chain var):chain)
antiprenexFreeVar fv (MonaFormulaEx2 [var] f) chain = antiprenexFreeVar (fvUpdateLocal fv (fst var) 2) f ((Exists2Chain var):chain)
antiprenexFreeVar fv (MonaFormulaAll0 [var] f) chain = antiprenexFreeVar (fvUpdateLocal fv var 0) f ((ForAll0Chain (var, Nothing)):chain)
antiprenexFreeVar fv (MonaFormulaAll1 [var] f) chain = antiprenexFreeVar (fvUpdateLocal fv (fst var) 1) f ((ForAll1Chain var):chain)
antiprenexFreeVar fv (MonaFormulaAll2 [var] f) chain = antiprenexFreeVar (fvUpdateLocal fv (fst var) 2) f ((ForAll2Chain var):chain)
antiprenexFreeVar _ atom@(MonaFormulaAtomic _) chain = flushQuantifChain chain atom
antiprenexFreeVar _ atom@(MonaFormulaPredCall _ _) chain = flushQuantifChain chain atom
antiprenexFreeVar _ atom@(MonaFormulaVar _) chain = flushQuantifChain chain atom
antiprenexFreeVar _ a _ = error $ "antiprenexFreeVar: not supported " ++ (show a)


antiprenexEmpty :: FormulaFV -> MonaFormula -> MonaFormula
antiprenexEmpty fv f = antiprenexFreeVar fv f []


--------------------------------------------------------------------------------------------------------------
-- Part with pure antiprenexing
--------------------------------------------------------------------------------------------------------------

propagateToSimple ::
  (MonaFormula -> MonaFormula -> MonaFormula)
  -> MonaFormula
  -> MonaFormula
  -> [QuantifVarChain]
  -> MonaFormula
propagateToSimple cons f1 f2 chain = flushQuantifChain remChain (cons (antiprenexFreeVarSimple f1 rem1) (antiprenexFreeVarSimple f2 rem2)) where --TODO: ex1 x where ..., y where ..., --> does not consider free variables in where declaration
  vars1 = freeVarsFormula f1
  vars2 = freeVarsFormula f2
  fv1 = filter (\a -> elem (getChainVarName a) vars1) chain
  fv2 = filter (\a -> elem (getChainVarName a) vars2) chain
  remChain = reverse $ intersect fv1 fv2
  rem1 = fv1 \\ remChain
  rem2 = fv2 \\ remChain

antiprenexFreeVarSimple :: MonaFormula -> [QuantifVarChain] -> MonaFormula
antiprenexFreeVarSimple (MonaFormulaNeg f) chain = flushQuantifChain chain (MonaFormulaNeg $ antiprenexFreeVarSimple f [])
antiprenexFreeVarSimple f@(MonaFormulaConj f1 f2) chain = propagateToSimple (MonaFormulaConj) f1 f2 chain
antiprenexFreeVarSimple (MonaFormulaDisj f1 f2) chain = MonaFormulaDisj (antiprenexFreeVarSimple f1 chain) (antiprenexFreeVarSimple f2 chain) -- propagateTo (MonaFormulaDisj) f1 f2 chain
antiprenexFreeVarSimple (MonaFormulaEx0 [var] f) chain = MonaFormulaEx0 [var] (antiprenexFreeVarSimple  f chain) --antiprenexFreeVar f ((Exists0Chain (var, Nothing)):chain)
antiprenexFreeVarSimple (MonaFormulaEx1 [var] f) chain = antiprenexFreeVarSimple  f ((Exists1Chain var):chain)
antiprenexFreeVarSimple (MonaFormulaEx2 [var] f) chain = antiprenexFreeVarSimple  f ((Exists2Chain var):chain)
antiprenexFreeVarSimple (MonaFormulaAll0 [var] f) chain = antiprenexFreeVarSimple  f ((ForAll0Chain (var, Nothing)):chain)
antiprenexFreeVarSimple (MonaFormulaAll1 [var] f) chain = antiprenexFreeVarSimple  f ((ForAll1Chain var):chain)
antiprenexFreeVarSimple (MonaFormulaAll2 [var] f) chain = antiprenexFreeVarSimple  f ((ForAll2Chain var):chain)
antiprenexFreeVarSimple atom@(MonaFormulaAtomic _) chain = flushQuantifChain chain atom
antiprenexFreeVarSimple atom@(MonaFormulaPredCall _ _) chain = flushQuantifChain chain atom
antiprenexFreeVarSimple atom@(MonaFormulaVar _) chain = flushQuantifChain chain atom
antiprenexFreeVarSimple a _ = error $ "antiprenexFreeVarSimple: not supported " ++ (show a)

antiprenexEmptySimple :: MonaFormula -> MonaFormula
antiprenexEmptySimple f = antiprenexFreeVarSimple f []


--------------------------------------------------------------------------------------------------------------
-- Part with the mona formula main antiprenexing
--------------------------------------------------------------------------------------------------------------

antiprenexFormula :: FormulaFV -> MonaFormula -> MonaFormula
antiprenexFormula varDecl f = distrLoop $ simplifyNegFormula $ moveNegToLeavesFormula $ simplifyNegFormula $ moveNegToLeavesFormula $ fBase where
  fBase = convertToBaseFormula f
  bal = if balanceFormulaConfig == BalFullTree then balanceFormula else id -- balanceFormula
  distrF = if distrConfig == DistrConservative then distributeFormula varDecl [] else distributeFormulaForce
  distr f = (iterate (fnc) f) !! distrSteps
  fnc f = if subFormulas f <= prefSubformulaCount then (distrF . antiprenexEmpty varDecl . simplifyNegFormula . moveNegToLeavesFormula) f else (antiprenexEmptySimple . simplifyNegFormula . moveNegToLeavesFormula) f
  pref fl = if subFormulas fl <= prefSubformulaCount then antiprenexEmpty varDecl fl else id fl
  distrLoop fl = if subFormulas fl <= antiprenexSubformulaCount then antiprenexEmpty varDecl $ bal $ distr fl else (iterate (simplifyNegFormula . moveNegToLeavesFormula . antiprenexEmptySimple) fl) !! distrSteps


antiprenexFormulaLight :: MonaFormula -> MonaFormula
antiprenexFormulaLight = antiprenexEmptySimple . simplifyNegFormula . moveNegToLeavesFormula . simplifyNegFormula . moveNegToLeavesFormula . convertToBaseFormula


convertDecl :: (MonaFormula -> MonaFormula) -> MonaDeclaration -> MonaDeclaration
convertDecl g (MonaDeclFormula f) = MonaDeclFormula $ g f
convertDecl g (MonaDeclVar0 decl) = MonaDeclVar0 decl
convertDecl g (MonaDeclVar1 [(var, decl)]) = MonaDeclVar1 [(var,decl >>= return . g)]
convertDecl g (MonaDeclVar2 [(var, decl)]) = MonaDeclVar2 [(var,decl >>= return . g)]
convertDecl g (MonaDeclPred name params f) = MonaDeclPred name params (g f) -- TODO: params are not converted
convertDecl g (MonaDeclMacro name params f) = MonaDeclMacro name params (g f)
convertDecl g (MonaDeclAssert f) = MonaDeclAssert $ g f
convertDecl g (MonaDeclConst atom) = MonaDeclConst atom -- TODO: antiprenexing is skipped
convertDecl g (MonaDeclLastpos var) = MonaDeclLastpos var
--convertDecl _ a = a -- TODO: incomplete


convertDeclFV :: FormulaFV -> (FormulaFV -> MonaFormula -> MonaFormula) -> MonaDeclaration -> MonaDeclaration
convertDeclFV fv g (MonaDeclFormula f) = MonaDeclFormula $ g fv f
convertDeclFV _ _ (MonaDeclVar0 decl) = MonaDeclVar0 decl
convertDeclFV fv g (MonaDeclVar1 [(var, decl)]) = MonaDeclVar1 [(var,decl >>= return . g fv)]
convertDeclFV fv g (MonaDeclVar2 [(var, decl)]) = MonaDeclVar2 [(var,decl >>= return . g fv)]
convertDeclFV fv g (MonaDeclPred name params f) = MonaDeclPred name params $ g (fvUpdateLocPredVars fv params) f -- TODO: params are not converted
convertDeclFV fv g (MonaDeclMacro name params f) = MonaDeclMacro name params $ g (fvUpdateLocPredVars fv params) f
convertDeclFV fv g (MonaDeclAssert f) = MonaDeclAssert $ g fv f
convertDeclFV _ _ (MonaDeclConst atom) = MonaDeclConst atom -- TODO: antiprenexing is skipped
convertDeclFV _ _ (MonaDeclLastpos var) = MonaDeclLastpos var
--convertDecl _ a = a -- TODO: incomplete


antiprenexFile :: MonaFile -> MonaFile
antiprenexFile (MonaFile dom decls) = MonaFile dom $ map (convertDeclFV varDecl (antiprenexFormula)) decls where
  varDecl = getMonaFormulaFV decls


antiprenexFileLight :: MonaFile -> MonaFile
antiprenexFileLight (MonaFile dom decls) = MonaFile dom $ map (convertDecl (antiprenexFormulaLight)) decls where


convertBaseFile :: MonaFile -> MonaFile
convertBaseFile (MonaFile dom decls) = MonaFile dom $ map (convertDecl (convertToBaseFormula)) decls where

--------------------------------------------------------------------------------------------------------------
-- Part with the shared subformula dividing
--------------------------------------------------------------------------------------------------------------

divideSharedFile :: MonaFile -> MonaFile
divideSharedFile (MonaFile dom decls) = MonaFile dom $ divideSh (fvMap decls) 0 decls where
  fvMap [] = Map.empty
  fvMap ((MonaDeclVar0 decl):xs) = Map.union (fvMap xs) $ Map.fromList $ zip decl [0,0..]
  fvMap ((MonaDeclVar1 decl):xs) = Map.union (fvMap xs) $ Map.fromList $ zip (map (fst) decl) [1,1..]
  fvMap ((MonaDeclVar2 decl):xs) = Map.union (fvMap xs) $ Map.fromList $ zip (map (fst) decl) [2,2..]
  fvMap (_:xs) = fvMap xs

  divideSh _ _ [] = []
  divideSh tm i ((MonaDeclFormula f):xs) = dcls' ++ ((MonaDeclFormula f'):(divideSh tm (i+(length dcls')) xs)) where
    (f', dcls') = divideSharedFormula tm i f
  divideSh tm i ((MonaDeclAssert f):xs) = dcls' ++ ((MonaDeclAssert f'):(divideSh tm (i+(length dcls')) xs)) where
    (f', dcls') = divideSharedFormula tm i f
  divideSh tm i (d:xs) = d:(divideSh tm i xs)


--------------------------------------------------------------------------------------------------------------
-- Part with the formula simplification
--------------------------------------------------------------------------------------------------------------

-- |Simplify formula: balance formula, move negations to leaves, simplify
-- formula (without antiprenexing).
simplifyFormula :: MonaFormula -> MonaFormula
simplifyFormula = simplifyNegFormula . moveNegToLeavesFormula . balanceFormula . simplifyNegFormula . moveNegToLeavesFormula . convertToBaseFormula


-- |Simplify MONA file: balance formula, move negations to leaves, simplify
-- formula (without antiprenexing).
simplifyFile :: MonaFile -> MonaFile
simplifyFile (MonaFile dom decls) = MonaFile dom $ map (convertDecl (simplifyFormula)) decls


--------------------------------------------------------------------------------------------------------------
-- Part with a conversion to formula without implications and equivalences.
--------------------------------------------------------------------------------------------------------------

convertToBaseAtom :: MonaAtom -> MonaFormula
convertToBaseAtom (MonaAtomNeq t1 t2) = MonaFormulaNeg $ MonaFormulaAtomic $ (MonaAtomEq t1 t2)
convertToBaseAtom atom = MonaFormulaAtomic atom


convertToBaseFormula :: MonaFormula -> MonaFormula
convertToBaseFormula (MonaFormulaAtomic atom) = convertToBaseAtom atom
convertToBaseFormula f@(MonaFormulaPredCall _ _) = f
convertToBaseFormula (MonaFormulaVar var) = MonaFormulaVar var
convertToBaseFormula (MonaFormulaNeg f) = MonaFormulaNeg (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaImpl f1 f2) = MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)
convertToBaseFormula (MonaFormulaEquiv f1 f2) = MonaFormulaConj (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f1) (convertToBaseFormula f2)) (MonaFormulaDisj (MonaFormulaNeg $ convertToBaseFormula f2) (convertToBaseFormula f1))
convertToBaseFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (convertToBaseFormula f)
convertToBaseFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (convertToBaseFormula f)




--------------------------------------------------------------------------------------------------------------
-- Part with negation simplifying.
--------------------------------------------------------------------------------------------------------------

moveNegToLeavesFormula :: MonaFormula -> MonaFormula
moveNegToLeavesFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
moveNegToLeavesFormula f@(MonaFormulaPredCall _ _) = f
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
simplifyNegFormula f@(MonaFormulaPredCall _ _) = f
simplifyNegFormula (MonaFormulaVar var) = MonaFormulaVar var
simplifyNegFormula (MonaFormulaNeg (MonaFormulaNeg f)) = simplifyNegFormula f
simplifyNegFormula (MonaFormulaNeg f) = MonaFormulaNeg (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (simplifyNegFormula f1) (simplifyNegFormula f2)
simplifyNegFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (simplifyNegFormula f)
simplifyNegFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (simplifyNegFormula f)
