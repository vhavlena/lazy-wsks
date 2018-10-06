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
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


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


-- |Unwind quantifiers of a formula, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifFormula :: MonaFormula -> MonaFormula
unwindQuantifFormula (MonaFormulaEx0 xs f) = foldr (\a g -> MonaFormulaEx0 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaEx1 xs f) = foldr (\a g -> MonaFormulaEx1 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaEx2 xs f) = foldr (\a g -> MonaFormulaEx2 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll0 xs f) = foldr (\a g -> MonaFormulaAll0 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll1 xs f) = foldr (\a g -> MonaFormulaAll1 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAll2 xs f) = foldr (\a g -> MonaFormulaAll2 [a] g) (unwindQuantifFormula f) xs
unwindQuantifFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
unwindQuantifFormula (MonaFormulaVar var) = MonaFormulaVar var
unwindQuantifFormula (MonaFormulaNeg f) = MonaFormulaNeg (unwindQuantifFormula f)
unwindQuantifFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (unwindQuantifFormula f1) (unwindQuantifFormula f2)
unwindQuantifFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (unwindQuantifFormula f1) (unwindQuantifFormula f2)


-- |Unwind quantifiers of a macro parameter, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifMacroParam :: MonaMacroParam -> [MonaMacroParam]
unwindQuantifMacroParam (MonaMacroParamVar0 vars) = map (\a -> MonaMacroParamVar0 [a]) vars
unwindQuantifMacroParam (MonaMacroParamVar1 vars) = map (\a -> MonaMacroParamVar1 [a]) vars
unwindQuantifMacroParam (MonaMacroParamVar2 vars) = map (\a -> MonaMacroParamVar2 [a]) vars
unwindQuantifMacroParam a = return a


-- |Unwind quantifiers of a declaration, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifDecl :: MonaDeclaration -> [MonaDeclaration]
unwindQuantifDecl (MonaDeclFormula f) = [MonaDeclFormula $ unwindQuantifFormula f]
unwindQuantifDecl (MonaDeclVar0 vars) = map (\a -> MonaDeclVar0 [a]) vars
unwindQuantifDecl (MonaDeclVar1 vars) = map (\a -> MonaDeclVar1 [a]) vars
unwindQuantifDecl (MonaDeclVar2 vars) = map (\a -> MonaDeclVar2 [a]) vars
unwindQuantifDecl (MonaDeclPred name params f) = [MonaDeclPred name (params >>= unwindQuantifMacroParam) (unwindQuantifFormula f)]
unwindQuantifDecl a = return a                                           -- TODO: need to be refined


-- |Unwind quantifiers of a mona file, i.e, ex1 x,y --> ex1 x: ex1 y
unwindQuantifFile :: MonaFile -> MonaFile
unwindQuantifFile (MonaFile dom decls) = MonaFile dom (decls >>= unwindQuantifDecl)


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
convertAtom :: MonaAtom -> Lo.Atom
convertAtom _ = Lo.Sing "X"
-- convertAtom atom = case (parseAtom atom) of
--    Nothing -> error $ "Parse error" ++ (show atom)
--    Just res -> res


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
-- replacePred args (MonaDeclPred _ params formula) | Dbg.trace ("\n" ++ show (map (mappred) (zip (expandPredParams params) args))) False = undefined  where
--     mappred ((MonaMacroParamVar0 vars),_) = head vars
--     mappred ((MonaMacroParamVar1 vars),_) = fst $ head vars
--     mappred ((MonaMacroParamVar2 vars),_) = fst $ head vars
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
substituteVars repl (MonaFormulaAtomic atom) = MonaFormulaAtomic $ substituteAtoms repl atom
substituteVars repl (MonaFormulaVar var) = MonaFormulaAtomic $  MonaAtomTerm $ substituteVar repl var
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


-- |Subtitute variable (given by its name) with a corresponding substitution term.
substituteVar :: [(MonaMacroParam, MonaTerm)] -> String -> MonaTerm
substituteVar repl var = Map.findWithDefault (MonaTermVar var) var sub
  where
    sub = Map.fromList $ map (mappred) repl
    mappred ((MonaMacroParamVar0 vars),b) = (head vars, b)
    mappred ((MonaMacroParamVar1 vars),b) = (fst $ head vars, b)
    mappred ((MonaMacroParamVar2 vars),b) = (fst $ head vars, b)


-- |Subtitute variables in atoms with corresponding substitutions (terms).
substituteAtoms :: [(MonaMacroParam, MonaTerm)] -> MonaAtom -> MonaAtom
substituteAtoms repl (MonaAtomLe t1 t2) = MonaAtomLe (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomLeq t1 t2) = MonaAtomLeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomGe t1 t2) = MonaAtomGe (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomGeq t1 t2) = MonaAtomGeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomEq t1 t2) = MonaAtomEq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomNeq t1 t2) = MonaAtomNeq (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomIn t1 t2) = MonaAtomIn (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomNotIn t1 t2) = MonaAtomNotIn (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomSub t1 t2) = MonaAtomSub (substituteTerms repl t1) (substituteTerms repl t2)
substituteAtoms repl (MonaAtomSing t) = MonaAtomSing $ substituteTerms repl t
substituteAtoms repl (MonaAtomEps t) = MonaAtomEps $ substituteTerms repl t
substituteAtoms repl t = t


-- |Subtitute variables in terms with corresponding substitutions (terms).
substituteTerms :: [(MonaMacroParam, MonaTerm)] -> MonaTerm -> MonaTerm
substituteTerms repl (MonaTermVar var) = substituteVar repl var
substituteTerms repl (MonaTermPlus t1 t2) = MonaTermPlus (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermMinus t1 t2) = MonaTermMinus (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermCat t1 t2) = MonaTermCat (substituteTerms repl t1) (substituteTerms repl t2)
substituteTerms repl (MonaTermUp t) = MonaTermUp (substituteTerms repl t)
substituteTerms repl t = t


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


-- |Assumes singleton quatified variables (i.e. after unwindQuantif function).
removeWhereFormula :: MonaFormula -> MonaFormula
removeWhereFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
removeWhereFormula (MonaFormulaVar var) = MonaFormulaVar var
removeWhereFormula (MonaFormulaNeg f) = MonaFormulaNeg (removeWhereFormula f)
removeWhereFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (removeWhereFormula f1) (removeWhereFormula f2)
removeWhereFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (removeWhereFormula f)
removeWhereFormula (MonaFormulaEx1 decl f) = expandWhereQuantif (MonaFormulaEx1) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaEx2 decl f) = expandWhereQuantif (MonaFormulaEx2) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll0 vars f) = MonaFormulaAll0 vars (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll1 decl f) = expandWhereQuantif (MonaFormulaAll1) decl (removeWhereFormula f)
removeWhereFormula (MonaFormulaAll2 decl f) = expandWhereQuantif (MonaFormulaAll2) decl (removeWhereFormula f)

expandWhereQuantif cons [(var, fwh)] f = cons [(var, Nothing)] (expand fwh f) where
  expand (Just f1) f2 = MonaFormulaConj f1 f2
  expand Nothing f2 = f2


removeWhereFile :: MonaFile -> MonaFile
removeWhereFile (MonaFile dom decls) = MonaFile dom (map (removeWhereDecl) decls)


removeWhereDecl :: MonaDeclaration -> MonaDeclaration
removeWhereDecl (MonaDeclFormula f) = MonaDeclFormula $ removeWhereFormula f
removeWhereDecl (MonaDeclPred name params f) = MonaDeclPred name params (removeWhereFormula f)
removeWhereDecl a = a  -- TODO: need to be refined



removeForAllFormula :: MonaFormula -> MonaFormula
removeForAllFormula (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
removeForAllFormula (MonaFormulaVar var) = MonaFormulaVar var
removeForAllFormula (MonaFormulaNeg f) = MonaFormulaNeg (removeForAllFormula f)
removeForAllFormula (MonaFormulaDisj f1 f2) = MonaFormulaDisj (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaConj f1 f2) = MonaFormulaConj (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaImpl f1 f2) = MonaFormulaImpl (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (removeForAllFormula f1) (removeForAllFormula f2)
removeForAllFormula (MonaFormulaEx0 vars f) = MonaFormulaEx0 vars (removeForAllFormula f)
removeForAllFormula (MonaFormulaEx1 decl f) = MonaFormulaEx1 decl (removeForAllFormula f)
removeForAllFormula (MonaFormulaEx2 decl f) = MonaFormulaEx2 decl (removeForAllFormula f)
removeForAllFormula (MonaFormulaAll0 vars f) = MonaFormulaNeg $ MonaFormulaEx0 vars (MonaFormulaNeg $ removeForAllFormula f)
removeForAllFormula (MonaFormulaAll1 decl f) = MonaFormulaNeg $ MonaFormulaEx1 decl (MonaFormulaNeg $ removeForAllFormula f)
removeForAllFormula (MonaFormulaAll2 decl f) = MonaFormulaNeg $ MonaFormulaEx2 decl (MonaFormulaNeg $ removeForAllFormula f)


removeForAllDecl :: MonaDeclaration -> MonaDeclaration
removeForAllDecl (MonaDeclFormula f) = MonaDeclFormula $ removeForAllFormula f
removeForAllDecl (MonaDeclVar0 [var]) = MonaDeclVar0 [var]
removeForAllDecl (MonaDeclVar1 [(var,f)]) = MonaDeclVar1 [(var, f >>= return . removeForAllFormula)]
removeForAllDecl (MonaDeclVar2 [(var,f)]) = MonaDeclVar2 [(var, f >>= return . removeForAllFormula)]
removeForAllDecl (MonaDeclPred name params f) = MonaDeclPred name params (removeForAllFormula f)  -- TODO: not considering complex declarations of parameters
removeForAllDecl a = a -- TODO: incomplete


removeForAllFile :: MonaFile -> MonaFile
removeForAllFile (MonaFile dom decls) = MonaFile dom (map (removeForAllDecl) decls)


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


-- |Definition of functor of QuantifChain
-- instance Functor QuantifChain where
--   fmap f EmptyChain = EmptyChain
--   fmap f (Exists0Chain val) = Exists0Chain (f val)
--   fmap f (Exists1Chain val) = Exists1Chain (f val)
--   fmap f (Exists2Chain val) = Exists2Chain (f val)
--   fmap f (ForAll0Chain val) = ForAll0Chain (f val)
--   fmap f (ForAll1Chain val) = ForAll1Chain (f val)
--   fmap f (ForAll2Chain val) = ForAll2Chain (f val)
--
--
-- -- |Definition of applicative functor of QuantifChain
-- instance Applicative QuantifChain where
--   pure = ExistsChain
--   EmptyChain <*> _ = EmptyChain
--   (Exists0Chain f) <*> st = fmap f st
--   (Exists1Chain f) <*> st = fmap f st
--   (ForAll0Chain f) <*> st = fmap f st
--   (ForAll1Chain f) <*> st = fmap f st
--   (ForAll2Chain f) <*> st = fmap f st
--
--
-- -- |Definition of Semigroup of QuantifChain
-- instance (Monoid a) => S.Semigroup (QuantifChain a) where
--   (<>) = mappend
--
--
-- -- |Definition of monoid of QuantifChain
-- instance (Monoid a) => Monoid (QuantifChain a) where
--   mempty = EmptyChain
--   mappend EmptyChain s = s
--   mappend s EmptyChain = s
--   mappend (ForAllChain v1) (ForAllChain v2) = ForAllChain (mappend v1 v2)
--   mappend (ExistsChain v1) (ExistsChain v2) = ExistsChain (mappend v1 v2)


freeVarsTerm :: MonaTerm -> [Lo.Var]
freeVarsTerm (MonaTermVar var) = [var]
freeVarsTerm (MonaTermConst num) = []
freeVarsTerm (MonaTermPlus t1 t2) = (freeVarsTerm t1) ++ (freeVarsTerm t2)
freeVarsTerm (MonaTermCat t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermMinus t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermUp t) = freeVarsTerm t


freeVarsAtom :: MonaAtom -> [Lo.Var]
freeVarsAtom (MonaAtomLe t1 t2) = (freeVarsTerm t1) ++ (freeVarsTerm t2)
freeVarsAtom (MonaAtomLeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomEq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomNeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomGe t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomGeq t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomIn t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomNotIn t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomSub t1 t2) = freeVarsAtom (MonaAtomLe t1 t2)
freeVarsAtom (MonaAtomEps t) = freeVarsTerm t
freeVarsAtom (MonaAtomSing t) = freeVarsTerm t
freeVarsAtom (MonaAtomTerm t) = freeVarsTerm t
freeVarsAtom MonaAtomTrue = []
freeVarsAtom MonaAtomFalse = []


freeVarsFormula :: MonaFormula -> [Lo.Var]
freeVarsFormula (MonaFormulaAtomic atom) = freeVarsAtom atom
freeVarsFormula (MonaFormulaVar var) = [var]
freeVarsFormula (MonaFormulaNeg f) = freeVarsFormula f
freeVarsFormula (MonaFormulaConj f1 f2) = nub $ (freeVarsFormula f1) ++ (freeVarsFormula f2)
freeVarsFormula (MonaFormulaDisj f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaImpl f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaEquiv f1 f2) = freeVarsFormula (MonaFormulaConj f1 f2)
freeVarsFormula (MonaFormulaEx0 [var] f) = delete var $ freeVarsFormula f
freeVarsFormula (MonaFormulaEx1 [var] f) = delete (fst var) $ freeVarsFormula f
freeVarsFormula (MonaFormulaEx2 [var] f) = delete (fst var) $ freeVarsFormula f
freeVarsFormula (MonaFormulaAll0 v f) = freeVarsFormula (MonaFormulaEx0 v f)
freeVarsFormula (MonaFormulaAll1 v f) = freeVarsFormula (MonaFormulaEx1 v f)
freeVarsFormula (MonaFormulaAll2 v f) = freeVarsFormula (MonaFormulaEx2 v f)
freeVarsFormula _ = error "freeVarsFormula: unimplemented" -- TODO: incomplete



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
antiprenexFormula f =  antiprenexFreeVar (moveNegToLeavesFormula $ convertToBaseFormula f) []


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


loadFormulas p = do
   file <- parseFile p
   let formulas = getFormulas file in
      putStrLn $ show $ convertBase2Simple $ convert2Base $ head formulas


flatTest file = do
  mona <- parseFile file
  putStrLn $ show mona
  putStrLn $ show $ antiprenexFile $ removeForAllFile $ removeWhereFile $ unwindQuantifFile $ replaceCalls mona
