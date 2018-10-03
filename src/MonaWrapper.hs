{-|
Module      : MonaWrapper
Description : Mona formulae wrapper
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaWrapper (
  getLogicFormula
  , getFormulas
) where

import Text.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.Prim
import Text.Parsec.String
import Text.Parsec.Token
import Data.List
import Data.Maybe

import MonaParser

--import qualified MonaParser as MoPa
import qualified Logic as Lo


-- |Convert Mona formula to Base Mona formula (without Ext1 quatifiers, only
-- basic logical connectives, ...).
convert2Base :: MonaFormula -> MonaFormula
convert2Base t@(MonaFormulaEx1 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaEx2 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaAll1 _ _) = unwindQuantif t
convert2Base t@(MonaFormulaAll2 _ _) = unwindQuantif t
convert2Base (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
convert2Base (MonaFormulaImpl f1 f2) = MonaFormulaDisj (MonaFormulaNeg $ convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaConj f1 f2) = MonaFormulaConj (convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaDisj f1 f2) = MonaFormulaDisj (convert2Base f1) (convert2Base f2)
convert2Base (MonaFormulaNeg f) = MonaFormulaNeg $ convert2Base f
convert2Base t = error $ "convert2Base: Unimplemented: " ++ (show t) -- TODO: Complete


-- |Unwind several chained quatifiers to chain of quatifiers (i.e.
-- Forall X1, X2 ---> Forall X1, Forall X2). Replace first order quatifiers as well.
unwindQuantif :: MonaFormula -> MonaFormula
-- unwindQuantif (MoPa.MonaFormulaEx1 [x] f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaEx1 (x:xs) f) = MoPa.MonaFormulaEx2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MonaFormulaEx1 [x] f) = MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaEx1 (x:xs) f) = MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MonaFormulaEx2 xs f))
unwindQuantif (MonaFormulaEx2 [x] f) = MonaFormulaEx2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaEx2 (x:xs) f) = MonaFormulaEx2 [(handleWhere x)] (unwindQuantif (MonaFormulaEx2 xs f))
-- unwindQuantif (MoPa.MonaFormulaAll1 [x] f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (convert2Base f) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
-- unwindQuantif (MoPa.MonaFormulaAll1 (x:xs) f) = MoPa.MonaFormulaAll2 [(handleWhere x)] (MoPa.MonaFormulaConj (unwindQuantif (MoPa.MonaFormulaEx1 xs f)) (MoPa.MonaFormulaAtomic ( "term sing "++ (fst x))))
unwindQuantif (MonaFormulaAll1 [x] f) = MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaAll1 (x:xs) f) = MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MonaFormulaAll2 xs f))

unwindQuantif (MonaFormulaAll2 [x] f) = MonaFormulaAll2 [(handleWhere x)] (convert2Base f)
unwindQuantif (MonaFormulaAll2 (x:xs) f) = MonaFormulaAll2 [(handleWhere x)] (unwindQuantif (MonaFormulaAll2 xs f))
unwindQuantif t = error $ "Unimplemented: " ++ (show t) -- TODO: Complete

-- |Hanle Mona variables declarations.
handleWhere :: (String, Maybe MonaFormula) -> (String, Maybe MonaFormula)
handleWhere = id


-- |Get Mona formulas from Mona file.
getFormulas :: MonaFile -> [MonaFormula]
getFormulas file = map (\(MonaDeclFormula f) -> f) $ filter (declFilter) (mf_decls file) where
   declFilter (MonaDeclFormula _) = True
   declFilter _ = False


-- |Parse Mona atom -- atoms are stored as strings.
parseAtom :: String -> Maybe Lo.Atom
parseAtom atom = parseSimpleAtom $ words atom


-- |Parse atom from a list containig 3 items [op1, operator, op2].
parseSimpleAtom :: [String] ->  Maybe Lo.Atom
parseSimpleAtom arr =
   if (length arr) /= 3 then Nothing
   else case arr !! 1 of
      "sing" -> Just $ Lo.Sing $ arr !! 2
      "sub" -> Just $ Lo.Subseteq (arr !! 0) (arr !! 2)
      --"cat1" -> Just $ Lo.Cat1 (arr !! 0) (arr !! 2)
      "eps" -> Just $ Lo.Eps $ arr !! 2
      "in" -> Just $ Lo.In (arr !! 0) (arr !! 2)
      "~=" -> Just $ Lo.Neq (arr !! 0) (arr !! 2)
      "=" -> Just $ Lo.Eqn (arr !! 0) (arr !! 2)
      "=.1" -> Just $ Lo.Cat2 (arr !! 0) (arr !! 2)
      "=.0" -> Just $ Lo.Cat1 (arr !! 0) (arr !! 2)


-- |Convert Mona string containing atom to Logic.Atom
convertAtom :: String -> Lo.Atom
convertAtom atom = case (parseAtom atom) of
   Nothing -> error $ "Parse error" ++ (show atom)
   Just res -> res


-- |Convert Mona base formula to Logic.Formula
convertBase2Simple :: MonaFormula -> Lo.Formula
convertBase2Simple (MonaFormulaAll2 [p] f) = Lo.ForAll (fst p) (convertBase2Simple f)
convertBase2Simple (MonaFormulaEx2 [p] f) = Lo.Exists (fst p) (convertBase2Simple f)
convertBase2Simple (MonaFormulaDisj f1 f2) = Lo.Disj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MonaFormulaConj f1 f2) = Lo.Conj (convertBase2Simple f1) (convertBase2Simple f2)
convertBase2Simple (MonaFormulaNeg f) = Lo.Neg $ convertBase2Simple f
convertBase2Simple (MonaFormulaAtomic atom) = Lo.FormulaAtomic $ convertAtom atom
convertBase2Simple t = error $ "Unimplemented: " ++ (show t)  -- TODO: Complete


getLogicFormula :: MonaFormula -> Lo.Formula
getLogicFormula = convertBase2Simple . convert2Base


-- |Replace calls of predicates with its body.
replaceCalls :: MonaFile -> MonaFile
replaceCalls (MonaFile dom decls) = MonaFile dom (replaceDecl [] decls)


-- |Replace calls of predicates with its body in mona declaration list.
replaceDecl :: [MonaDeclaration] -> [MonaDeclaration] -> [MonaDeclaration]
replaceDecl _ [] = []
replaceDecl done (x:xs) = conv:(replaceDecl (done ++ [conv]) xs) where
    conv = case x of
      MonaDeclPred name pars fle -> MonaDeclPred name pars (replaceFormulas done fle)
      MonaDeclFormula fle -> MonaDeclFormula $ replaceFormulas done fle
      MonaDeclVar1 vardecl -> MonaDeclVar1 $ applyVarDecl (replaceFormulas done) vardecl
      MonaDeclVar2 vardecl -> MonaDeclVar2 $ applyVarDecl (replaceFormulas done) vardecl
      a -> error $ "Unsupported formula: " ++ (show a)


-- |Replace pred calls in a given formula with already flattened declarations. No
-- cyclic dependency is allowed.
replaceFormulas :: [MonaDeclaration] -> MonaFormula -> MonaFormula
replaceFormulas decls f@(MonaFormulaAtomic _) = f
replaceFormulas decls f@(MonaFormulaVar _) = f
replaceFormulas decls (MonaFormulaNeg f) = MonaFormulaNeg (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaDisj f1 f2) = MonaFormulaDisj (replaceFormulas decls f1) (replaceFormulas decls f2)
replaceFormulas decls (MonaFormulaConj f1 f2) = MonaFormulaConj (replaceFormulas decls f1) (replaceFormulas decls f2)
replaceFormulas decls (MonaFormulaImpl f1 f2) = MonaFormulaImpl (replaceFormulas decls f1) (replaceFormulas decls f2)
replaceFormulas decls (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (replaceFormulas decls f1) (replaceFormulas decls f2)
replaceFormulas decls (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaEx1 vardecl f) = MonaFormulaEx1 (applyVarDecl (replaceFormulas decls) vardecl) (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaEx2 vardecl f) = MonaFormulaEx2 (applyVarDecl (replaceFormulas decls) vardecl) (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaAll1 vardecl f) = MonaFormulaAll1 (applyVarDecl (replaceFormulas decls) vardecl) (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaAll2 vardecl f) = MonaFormulaAll2 (applyVarDecl (replaceFormulas decls) vardecl) (replaceFormulas decls f)
replaceFormulas decls (MonaFormulaPredCall name params) = fromJust $ find (filterMacro name) decls >>= replacePred params


-- |Replace a predicate call (given arguments) with predicate body.
replacePred :: [MonaTerm] -> MonaDeclaration -> Maybe MonaFormula
replacePred args (MonaDeclPred _ params formula) = return $ substituteVars (zip (expandPredParams params) args) formula


-- |Expand variables in predicate declaration into singleton variable declaration -- ex2 X,Y --> ex2 X, ex2 Y
expandPredParams :: [MonaMacroParam] -> [MonaMacroParam]
expandPredParams xs = xs >>= expand where
  expand (MonaMacroParamVar0 a) = a >>= \x -> return $ MonaMacroParamVar0 [x]
  expand (MonaMacroParamVar1 a) = a >>= \x -> return $ MonaMacroParamVar1 [x]
  expand (MonaMacroParamVar2 a) = a >>= \x -> return $ MonaMacroParamVar2 [x]


-- |Filter mona declarations that have a specified name.
filterMacro :: String -> MonaDeclaration -> Bool
filterMacro name f@(MonaDeclPred nm _ _) = nm == name
filterMacro name _ = False


-- |Substitute variables with mona terms (does not check whether variables are
-- of appropriate types).
-- arg1: MonaMacroParam (parameter of a predicate), MonaTerm (term that should
-- replaced the macro parameter)
substituteVars :: [(MonaMacroParam, MonaTerm)] -> MonaFormula -> MonaFormula
substituteVars repl f@(MonaFormulaAtomic _) = f
substituteVars repl (MonaFormulaVar var) = case find (==var) (map (mappred) repl) of
  (Just val) -> MonaFormulaVar val
  Nothing -> MonaFormulaVar var
  where
    mappred ((MonaMacroParamVar0 vars),_) = head vars
    mappred ((MonaMacroParamVar1 vars),_) = fst $ head vars
    mappred ((MonaMacroParamVar2 vars),_) = fst $ head vars
substituteVars repl (MonaFormulaNeg f) = MonaFormulaNeg (substituteVars repl f)
substituteVars repl (MonaFormulaDisj f1 f2) = MonaFormulaDisj (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaConj f1 f2) = MonaFormulaConj (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaImpl f1 f2) = MonaFormulaImpl (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (substituteVars repl f1) (substituteVars repl f2)
substituteVars repl (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (substituteVars repl' f) where
  repl' = filter (\a -> not $ elem (varFromMacroParam a) vars) repl
substituteVars repl (MonaFormulaEx1 vardecl f) = MonaFormulaEx1 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaEx2 vardecl f) = MonaFormulaEx2 vardecl'  (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (substituteVars repl' f) where
  repl' = filter (\a -> not $ elem (varFromMacroParam a) vars) repl
substituteVars repl (MonaFormulaAll1 vardecl f) = MonaFormulaAll1 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl (MonaFormulaAll2 vardecl f) = MonaFormulaAll2 vardecl' (substituteVars repl' f) where
  vardecl' = applyVarDecl (substituteVars repl') vardecl
  repl' = filterSubst vardecl repl
substituteVars repl _ = error "Cyclic dependecy between predicates"


-- |Filter substitutions (remove substitutions that are in var list).
-- arg1: varlist (list of quantified variables)
-- arg2: given substitution
filterSubst :: [(String, Maybe MonaFormula)] -> [(MonaMacroParam, MonaTerm)] -> [(MonaMacroParam, MonaTerm)]
filterSubst vars = filter (\a -> not $ elem (varFromMacroParam a) vars')
  where
    vars' = map (fst) vars


-- |Get variable name from mona macro param.
varFromMacroParam :: (MonaMacroParam, MonaTerm) -> String
varFromMacroParam ((MonaMacroParamVar0 vars),_) = head vars
varFromMacroParam ((MonaMacroParamVar1 vars),_) = fst $ head vars
varFromMacroParam ((MonaMacroParamVar2 vars),_) = fst $ head vars


-- |Apply function on list of variable declarations.
applyVarDecl :: (MonaFormula -> MonaFormula) -> [(String, Maybe MonaFormula)] -> [(String, Maybe MonaFormula)]
applyVarDecl f = map (\(a,b) -> (a,b >>= \a -> return $ f a))

loadFormulas p = do
   file <- parseFile p
   let formulas = getFormulas file in
      putStrLn $ show $ convertBase2Simple $ convert2Base $ head formulas


flatTest file = do
  mona <- parseFile file
  putStrLn $ show mona
  putStrLn $ show $ replaceCalls mona
