{-|
Module      : MonaFormulaDistr
Description : Mona formulae distributivity
Author      : Vojtech Havlena, 2019
License     : GPL-3
-}

module MonaFormulaDistr where

import Data.List
import Data.Maybe
import MonaParser
import MonaFormulaOperationSubst

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Ord as Ord
import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with the types
--------------------------------------------------------------------------------------------------------------

type FVType = Map.Map String Int
type SubFVType = Set.Set (String, Int)
type SubformulaType = (MonaFormula, SubFVType)


distributeFormula :: [String] -> MonaFormula -> MonaFormula
distributeFormula _ (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
distributeFormula _ f@(MonaFormulaPredCall _ _) = f
distributeFormula _ (MonaFormulaVar var) = MonaFormulaVar var
distributeFormula _ (MonaFormulaNeg f) = MonaFormulaNeg (distributeFormula [] f)
distributeFormula c (MonaFormulaDisj f1 f2) = MonaFormulaDisj (distributeFormula c f1) (distributeFormula c f2)
distributeFormula c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
  if (length c) /= 0 && isDistrSuit f1 then MonaFormulaDisj (distributeFormula c (MonaFormulaConj f1 f2)) (distributeFormula c (MonaFormulaConj f1 f3))
  else (MonaFormulaConj (distributeFormula [] f1) (distributeFormula [] (MonaFormulaDisj f2 f3)))
distributeFormula c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
  if (length c) /= 0 && isDistrSuit f1 then MonaFormulaDisj (distributeFormula c (MonaFormulaConj f2 f1)) (distributeFormula c (MonaFormulaConj f3 f1))
  else MonaFormulaConj (distributeFormula c (MonaFormulaDisj f2 f3)) (distributeFormula c f1)
distributeFormula c (MonaFormulaConj f1 f2) = MonaFormulaConj (distributeFormula [] f1) (distributeFormula [] f2)
distributeFormula c (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (distributeFormula ("x":c) f)
distributeFormula c (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (distributeFormula ("x":c) f)
distributeFormula c (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (distributeFormula ("x":c) f)


-- |Compute number of conjunctions and disjunctions on the top of the formula.
conjDisjTop :: MonaFormula -> Int
conjDisjTop (MonaFormulaPredCall _ _) = 0
conjDisjTop (MonaFormulaAtomic _) = 0
conjDisjTop (MonaFormulaVar _) = 0
conjDisjTop (MonaFormulaNeg _) = 0
conjDisjTop (MonaFormulaConj f1 f2) = 1 + (conjDisjTop f1) + (conjDisjTop f2)
conjDisjTop (MonaFormulaDisj f1 f2) = 1 + (conjDisjTop f1) + (conjDisjTop f2)
conjDisjTop (MonaFormulaEx0 _ f) = 0
conjDisjTop (MonaFormulaEx1 _ f) = 0
conjDisjTop (MonaFormulaEx2 _ f) = 0


-- |Is it suitable to use distributivity?
isDistrSuit :: MonaFormula -> Bool
isDistrSuit f = ((conjDisjTop f) > 10 ) || ((conjDisjTop f) <= 10 && isDistrPredSuit f)


-- |Is it suitable to use distributivity (based on the predicate calls)
isDistrPredSuit :: MonaFormula -> Bool
isDistrPredSuit (MonaFormulaPredCall _ l) = (length l) <= 5
isDistrPredSuit (MonaFormulaAtomic atom) = True
isDistrPredSuit (MonaFormulaVar var) = True
isDistrPredSuit fl@(MonaFormulaNeg f) = isDistrPredSuit f
isDistrPredSuit fl@(MonaFormulaConj f1 f2) = (isDistrPredSuit f1) && (isDistrPredSuit f2)
isDistrPredSuit fl@(MonaFormulaDisj f1 f2) = (isDistrPredSuit f1) && (isDistrPredSuit f2)
isDistrPredSuit fl@(MonaFormulaEx0 [var] f) = isDistrPredSuit f
isDistrPredSuit fl@(MonaFormulaEx1 [(var, Nothing)] f) = isDistrPredSuit f
isDistrPredSuit fl@(MonaFormulaEx2 [(var, Nothing)] f) = isDistrPredSuit f



distributeFormulaForce :: MonaFormula -> MonaFormula
distributeFormulaForce (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
distributeFormulaForce f@(MonaFormulaPredCall _ _) = f
distributeFormulaForce (MonaFormulaVar var) = MonaFormulaVar var
distributeFormulaForce (MonaFormulaNeg f) = MonaFormulaNeg (distributeFormulaForce f)
distributeFormulaForce (MonaFormulaDisj f1 f2) = MonaFormulaDisj (distributeFormulaForce f1) (distributeFormulaForce f2)
distributeFormulaForce (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
  MonaFormulaDisj (distributeFormulaForce (MonaFormulaConj f1 f2)) (distributeFormulaForce (MonaFormulaConj f1 f3))
distributeFormulaForce (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
  MonaFormulaDisj (distributeFormulaForce (MonaFormulaConj f2 f1)) (distributeFormulaForce (MonaFormulaConj f3 f1))
distributeFormulaForce (MonaFormulaConj f1 f2) = MonaFormulaConj (distributeFormulaForce f1) (distributeFormulaForce f2)
distributeFormulaForce (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (distributeFormulaForce f)
distributeFormulaForce (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (distributeFormulaForce f)
distributeFormulaForce (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (distributeFormulaForce f)


--
-- applyConc1 :: (MonaFormula -> MonaFormula)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
-- applyConc1 f (fr, rr) = (f fr, rr)
--
--
-- applyConc2 :: (MonaFormula -> MonaFormula -> MonaFormula)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
--   -> (MonaFormula, MonaDeclaration)
-- applyConc2 f (fr1, rr1) (fr2, rr2) = (f fr1 fr2, rr1 ++ rr2)
--
--
-- getFormulaShare :: Map.Map String Int
--   -> [String]
--   -> MonaFormula
--   -> [MonaDeclaration]
-- getFormulaShare _ _ (MonaFormulaAtomic atom) = []
-- getFormulaShare _ _ f@(MonaFormulaPredCall _ _) = []
-- getFormulaShare _ _ (MonaFormulaVar var) = []
-- getFormulaShare mp _ (MonaFormulaNeg f) = getFormulaShare mp [] f
-- getFormulaShare mp c (MonaFormulaDisj f1 f2) = (getFormulaShare mp c f1) ++ (getFormulaShare mp c f2)
-- getFormulaShare mp c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
--   if (length c) /= 0 then (createPred mp "predTmp" f1):(getFormulaShare mp c (MonaFormulaConj f1 f2)) ++ (getFormulaShare mp c (MonaFormulaConj f1 f3))
--   else  (getFormulaShare mp [] f1) ++ (getFormulaShare mp [] (MonaFormulaDisj f2 f3))
-- getFormulaShare mp c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
--   if (length c) /= 0 then (createPred mp "predTmp" f1):(getFormulaShare mp c (MonaFormulaConj f2 f1)) ++ (getFormulaShare mp c (MonaFormulaConj f3 f1))
--   else (getFormulaShare mp c (MonaFormulaDisj f2 f3)) ++ (getFormulaShare mp c f1)
-- getFormulaShare mp c (MonaFormulaConj f1 f2) = (getFormulaShare mp [] f1) ++ (getFormulaShare mp [] f2)
-- getFormulaShare mp c (MonaFormulaEx0 [var] f) = getFormulaShare (Map.insert var 0 mp) ("x":c) f
-- getFormulaShare mp c (MonaFormulaEx1 [decl] f) = getFormulaShare (Map.insert (fst decl) 1 mp) ("x":c) f
-- getFormulaShare mp c (MonaFormulaEx2 [decl] f) = getFormulaShare (Map.insert (fst decl) 2 mp) ("x":c) f


freeVarsType :: FVType -> MonaFormula -> SubFVType
freeVarsType tm fl = Set.fromList $ map (\x -> (x, tm Map.! x)) $ freeVarsFormula fl


baseCaseMap :: FVType -> MonaFormula -> Map.Map SubformulaType Int
baseCaseMap tm fl = Map.singleton (fl, freeVarsType tm fl) 1


createSubformulaMap :: FVType -> MonaFormula -> Map.Map SubformulaType Int
createSubformulaMap tm (MonaFormulaAtomic atom) = Map.empty -- baseCaseMap tm a
createSubformulaMap tm (MonaFormulaVar var) = Map.empty -- baseCaseMap tm a
createSubformulaMap tm (MonaFormulaPredCall _ _) = Map.empty
createSubformulaMap tm fl@(MonaFormulaNeg f) = Map.unionWith (+) (baseCaseMap tm fl) (createSubformulaMap tm f)
createSubformulaMap tm fl@(MonaFormulaConj f1 f2) = Map.unionsWith (+) [(baseCaseMap tm fl), (createSubformulaMap tm f1), (createSubformulaMap tm f2)]
createSubformulaMap tm fl@(MonaFormulaDisj f1 f2) = Map.unionsWith (+) [(baseCaseMap tm fl), (createSubformulaMap tm f1), (createSubformulaMap tm f2)]
createSubformulaMap tm fl@(MonaFormulaEx0 [var] f) = Map.unionWith (+) (baseCaseMap tm fl) (createSubformulaMap (Map.insert var 0 tm) f)
createSubformulaMap tm fl@(MonaFormulaEx1 [(var, Nothing)] f) = Map.unionWith (+) (baseCaseMap tm fl) (createSubformulaMap (Map.insert var 1 tm) f)
createSubformulaMap tm fl@(MonaFormulaEx2 [(var, Nothing)] f) = Map.unionWith (+) (baseCaseMap tm fl) (createSubformulaMap (Map.insert var 2 tm) f)


createPredicateMap :: [SubformulaType] -> Int -> (Map.Map SubformulaType MonaFormula, [MonaDeclaration])
createPredicateMap lst i = (Map.fromList $ createPredCall i lst', createPredDecl i lst') where
  lst' = map (\(x,y) -> (x,Set.toList y)) lst
  createPredCall _ [] = []
  createPredCall i ((fl,fv):xs) = ((fl,Set.fromList fv), MonaFormulaPredCall name (map (MonaTermVar . fst) fv)):(createPredCall (i+1) xs) where
    name = "predTmp" ++ (show i)
  createPredDecl _ [] = []
  createPredDecl i ((fl,fv):xs) = (MonaDeclPred name (map (projFV) fv) fl):(createPredDecl (i+1) xs) where
    name = "predTmp" ++ (show i)
    projFV (var,0) = MonaMacroParamVar0 [var]
    projFV (var,1) = MonaMacroParamVar1 [(var, Nothing)]
    projFV (var,2) = MonaMacroParamVar2 [(var, Nothing)]


lookupProceed :: FVType -> Map.Map SubformulaType MonaFormula -> MonaFormula -> MonaFormula
lookupProceed tm mp fl = case (Map.lookup (fl, freeVarsType tm fl) mp) of
    Nothing -> replaceSharedFormula tm mp fl
    Just rfl -> rfl

replaceSharedFormula :: FVType -> Map.Map SubformulaType MonaFormula -> MonaFormula -> MonaFormula
replaceSharedFormula _ _ a@(MonaFormulaAtomic atom) = a
replaceSharedFormula _ _ a@(MonaFormulaVar var) = a
replaceSharedFormula _ _ a@(MonaFormulaPredCall _ _) = a
replaceSharedFormula tm fm (MonaFormulaNeg f) = MonaFormulaNeg $ lookupProceed tm fm f
replaceSharedFormula tm fm (MonaFormulaConj f1 f2) = MonaFormulaConj (lookupProceed tm fm f1) (lookupProceed tm fm f2)
replaceSharedFormula tm fm (MonaFormulaDisj f1 f2) = MonaFormulaDisj (lookupProceed tm fm f1) (lookupProceed tm fm f2)
replaceSharedFormula tm fm (MonaFormulaEx0 [var] f) = MonaFormulaEx0 [var] $ lookupProceed (Map.insert var 0 tm) fm f
replaceSharedFormula tm fm (MonaFormulaEx1 [(var, Nothing)] f) = MonaFormulaEx1 [(var, Nothing)] $ lookupProceed (Map.insert var 1 tm) fm f
replaceSharedFormula tm fm (MonaFormulaEx2 [(var, Nothing)] f) = MonaFormulaEx2 [(var, Nothing)] $ lookupProceed (Map.insert var 2 tm) fm f


divideSharedFormula :: FVType -> Int -> MonaFormula -> (MonaFormula, [MonaDeclaration])
divideSharedFormula tm i f = (replaceSharedFormula tm mp f, decls) where
  smp = createSubformulaMap tm f
  fltSmp =  map (fst) $ take 60 $ sortOn (negate . formulaCountSubFle . fst . fst) $ filter (\x -> (snd x) >= 8) $ sortOn (negate . snd) $ Map.toList smp
  (mp, decls) = createPredicateMap fltSmp i


formulaCountSubFle :: MonaFormula -> Int
formulaCountSubFle (MonaFormulaExGen _ f) = formulaCountSubFle f
formulaCountSubFle (MonaFormulaConj f1 f2) = (formulaCountSubFle f1) + (formulaCountSubFle f2)
formulaCountSubFle _ = 1


-- createPred :: Map.Map String Int -> String -> MonaFormula -> MonaDeclaration
-- createPred mp name f = MonaDeclPred name params f where
--   fvs = freeVarsFormula f
--   params = map (\x -> conv x $ mp Map.! x) fvs
--   conv name 0 = MonaMacroParamVar0 [name]
--   conv name 1 = MonaMacroParamVar1 [(name, Nothing)]
--   conv name 2 = MonaMacroParamVar2 [(name, Nothing)]


-- replaceSharedFormula :: Map.Map MonaFormula String
--   -> [String]
--   -> MonaFormula
--   -> MonaFormula
-- replaceSharedFormula _ _ (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
-- replaceSharedFormula _ _ f@(MonaFormulaPredCall _ _) = f
-- replaceSharedFormula _ _ (MonaFormulaVar var) = MonaFormulaVar var
-- replaceSharedFormula mp _ (MonaFormulaNeg f) = MonaFormulaNeg (replaceSharedFormula mp [] f)
-- replaceSharedFormula mp c (MonaFormulaDisj f1 f2) = MonaFormulaDisj (replaceSharedFormula mp c f1) (replaceSharedFormula mp c f2)
-- replaceSharedFormula mp c (MonaFormulaConj f1 (MonaFormulaDisj f2 f3)) =
--   if (length c) /= 0 then MonaFormulaDisj (replaceSharedFormula mp c (MonaFormulaConj cl f2)) (replaceSharedFormula mp c (MonaFormulaConj cl f3))
--   else (MonaFormulaConj (replaceSharedFormula mp [] f1) (replaceSharedFormula mp [] (MonaFormulaDisj f2 f3))) where
--     cl = replaceFormulaPred f1 mp
-- replaceSharedFormula mp c (MonaFormulaConj (MonaFormulaDisj f2 f3) f1) =
--   if (length c) /= 0 then MonaFormulaDisj (replaceSharedFormula mp c (MonaFormulaConj f2 cl)) (replaceSharedFormula mp c (MonaFormulaConj f3 cl))
--   else MonaFormulaConj (replaceSharedFormula mp c (MonaFormulaDisj f2 f3)) (replaceSharedFormula mp c f1) where
--     cl = replaceFormulaPred f1 mp
-- replaceSharedFormula mp c (MonaFormulaConj f1 f2) = MonaFormulaConj (replaceSharedFormula mp [] f1) (replaceSharedFormula mp [] f2)
-- replaceSharedFormula mp c (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (replaceSharedFormula mp ("x":c) f)
-- replaceSharedFormula mp c (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (replaceSharedFormula mp ("x":c) f)
-- replaceSharedFormula mp c (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (replaceSharedFormula mp ("x":c) f)


-- replaceFormulaPred :: MonaFormula -> Map.Map MonaFormula String -> MonaFormula
-- replaceFormulaPred f mp = MonaFormulaPredCall name params  where
--   fvs = freeVarsFormula f
--   name = mp Map.! f
--   params = map (MonaTermVar) fvs
