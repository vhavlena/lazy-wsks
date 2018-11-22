{-|
Module      : MonaFormulaOperation
Description : Mona formulae operations.
Author      : Vojtech Havlena, 2018
License     : GPL-3
-}

module MonaFormulaOperation where

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

import qualified Logic as Lo
import qualified FormulaOperation as Fo
import qualified Data.Map as Map
import qualified Debug.Trace as Dbg


--------------------------------------------------------------------------------------------------------------
-- Part with unwinding quantifiers (ex2 X,Y: ---> ex2 X: ex2 Y:)
--------------------------------------------------------------------------------------------------------------

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
unwindQuantifFormula (MonaFormulaPredCall s t) = MonaFormulaPredCall s t


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


--------------------------------------------------------------------------------------------------------------
-- Part with formula flattening (removing predicate calls).
--------------------------------------------------------------------------------------------------------------

-- |Replace calls of predicates with its body.
replaceCallsFile :: MonaFile -> MonaFile
replaceCallsFile (MonaFile dom decls) = MonaFile dom (replaceCallsDecl [] decls)


-- |Replace calls of predicates with its body in mona declaration list.
replaceCallsDecl :: [MonaDeclaration] -> [MonaDeclaration] -> [MonaDeclaration]
replaceCallsDecl _ [] = []
replaceCallsDecl done (x:xs) = conv:(replaceCallsDecl (done ++ [conv]) xs) where
    conv = case x of
      MonaDeclPred name pars fle -> MonaDeclPred name pars (replaceCallsFormulas done fle)
      MonaDeclFormula fle -> MonaDeclFormula $ replaceCallsFormulas done fle
      MonaDeclVar1 vardecl -> MonaDeclVar1 $ applyVarDecl (replaceCallsFormulas done) vardecl
      MonaDeclVar2 vardecl -> MonaDeclVar2 $ applyVarDecl (replaceCallsFormulas done) vardecl
      a -> error $ "Unsupported formula: " ++ (show a)


-- |Replace pred calls in a given formula with already flattened declarations. No
-- cyclic dependency is allowed.
replaceCallsFormulas :: [MonaDeclaration] -> MonaFormula -> MonaFormula
replaceCallsFormulas decls f@(MonaFormulaAtomic _) = f
replaceCallsFormulas decls f@(MonaFormulaVar _) = f
replaceCallsFormulas decls (MonaFormulaNeg f) = MonaFormulaNeg (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaDisj f1 f2) =
    MonaFormulaDisj (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaConj f1 f2) =
    MonaFormulaConj (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaImpl f1 f2) =
    MonaFormulaImpl (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaEquiv f1 f2) =
    MonaFormulaEquiv (replaceCallsFormulas decls f1) (replaceCallsFormulas decls f2)
replaceCallsFormulas decls (MonaFormulaEx0 vars f) =
    MonaFormulaEx0 vars (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaEx1 vardecl f) =
    MonaFormulaEx1 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaEx2 vardecl f) =
    MonaFormulaEx2 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll0 vars f) =
    MonaFormulaAll0 vars (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll1 vardecl f) =
    MonaFormulaAll1 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaAll2 vardecl f) =
    MonaFormulaAll2 (applyVarDecl (replaceCallsFormulas decls) vardecl) (replaceCallsFormulas decls f)
replaceCallsFormulas decls (MonaFormulaPredCall name params) =
    fromJust $ find (filterMacro name) decls >>= replacePred params


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


--------------------------------------------------------------------------------------------------------------
-- Part with variables substitutions.
--------------------------------------------------------------------------------------------------------------

-- |Substitute variables with mona terms (does not check whether variables are
-- of appropriate types).
-- arg1: MonaMacroParam (parameter of a predicate), MonaTerm (term that should
-- replaced the macro parameter)
substituteVars :: [(MonaMacroParam, MonaTerm)] -> MonaFormula -> MonaFormula
substituteVars repl (MonaFormulaPredCall name terms) = MonaFormulaPredCall name $ map (substituteTerms repl) terms
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
--substituteVars repl _ = error "Cyclic dependecy between predicates"


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
substituteAtoms repl (MonaAtomTerm t) = MonaAtomTerm $ substituteTerms repl t
--substituteAtoms repl t = t


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


--------------------------------------------------------------------------------------------------------------
-- Part with removing where construction.
--------------------------------------------------------------------------------------------------------------

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


--------------------------------------------------------------------------------------------------------------
-- Part with removing universal quantification.
--------------------------------------------------------------------------------------------------------------

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
-- Part with renaming bound variables.
--------------------------------------------------------------------------------------------------------------

renameBVFile :: MonaFile -> MonaFile
renameBVFile (MonaFile dom decls) = MonaFile dom (renameBVDecl [] decls [])


renameBVDecl :: [MonaDeclaration] -> [MonaDeclaration] -> [Lo.Var] -> [MonaDeclaration]
renameBVDecl _ [] _ = []
renameBVDecl done (x:xs) vars = conv:(renameBVDecl (done ++ [conv]) xs (vars ++ v)) where
    conv = case x of
      MonaDeclPred name pars fle -> MonaDeclPred name pars (renameBVFormula vars fle)
      MonaDeclFormula fle -> MonaDeclFormula $ renameBVFormula vars fle
      MonaDeclVar1 vardecl -> MonaDeclVar1 $ renameBVForDecl vardecl vars
      MonaDeclVar2 vardecl -> MonaDeclVar2 $ renameBVForDecl vardecl vars
      a -> error $ "Unsupported formula: " ++ (show a)
    v = varsDecl conv


renameBVForDecl :: [(String, Maybe MonaFormula)] -> [Lo.Var] -> [(String, Maybe MonaFormula)]
renameBVForDecl [] _ = []
renameBVForDecl ((var,f):xs) vars =
  if elem var vars then (new, f >>= \a -> Just $ substituteVars repl a):(renameBVForDecl xs (new:vars))
  else  (var,f):(renameBVForDecl xs (var:vars)) where
    new = getNewVarName (vars ++ vars') 0
    repl = [(MonaMacroParamVar1 [(var, Nothing)], MonaTermVar new)]
    vars' = case f of
      Just a -> varsFormula a
      Nothing -> []


-- Works for formulae without forall
renameBVFormula :: [Lo.Var] -> MonaFormula -> MonaFormula
renameBVFormula vars t@(MonaFormulaPredCall name terms) = t
renameBVFormula vars (MonaFormulaAtomic atom) = MonaFormulaAtomic atom
renameBVFormula vars (MonaFormulaVar var) = MonaFormulaVar var
renameBVFormula vars (MonaFormulaNeg f) = MonaFormulaNeg (renameBVFormula vars f)
renameBVFormula vars (MonaFormulaDisj f1 f2) = MonaFormulaDisj (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaConj f1 f2) = MonaFormulaConj (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaImpl f1 f2) = MonaFormulaImpl (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaEquiv f1 f2) = MonaFormulaEquiv (renameBVFormula vars f1) (renameBVFormula vars f2)
renameBVFormula vars (MonaFormulaEx0 [var] f) = handleQuantifRename vars var f var (MonaFormulaEx0) (fst)
renameBVFormula vars (MonaFormulaEx1 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaEx1) (id)
renameBVFormula vars (MonaFormulaEx2 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaEx2) (id)
renameBVFormula vars (MonaFormulaAll0 [var] f) = handleQuantifRename vars var f var (MonaFormulaAll0) (fst)
renameBVFormula vars (MonaFormulaAll1 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaAll1) (id)
renameBVFormula vars (MonaFormulaAll2 [decl] f) = handleQuantifRename vars (fst decl) f decl (MonaFormulaAll2) (id)
renameBVFormula vars t = error $ "renameBVFormula: " ++ show t


handleQuantifRename :: [Lo.Var] -> Lo.Var -> MonaFormula -> a -> ([a] -> MonaFormula -> MonaFormula) -> ((String, Maybe MonaFormula) -> a) -> MonaFormula
handleQuantifRename vars var f decl cons proj =
  if (elem var vars) then cons [decl] (renameBVFormula (var:vars) f)
  else cons decl' (renameBVFormula (new:vars) f') where
    repl = [(MonaMacroParamVar1 [(var, Nothing)], MonaTermVar new)]
    new = getNewVarName (vars ++ (varsFormula f)) 0
    f' = substituteVars repl f
    decl' = [proj (new, Nothing)]

getNewVarName :: [Lo.Var] -> Int -> Lo.Var
getNewVarName lst i =
  if elem var lst then getNewVarName lst (i+1)
  else var where
    var = "T" ++ (show i)


--------------------------------------------------------------------------------------------------------------
-- Part with (free) variables determination.
--------------------------------------------------------------------------------------------------------------

freeVarsTerm :: MonaTerm -> [Lo.Var]
freeVarsTerm (MonaTermVar var) = [var]
freeVarsTerm (MonaTermConst num) = []
freeVarsTerm (MonaTermPlus t1 t2) = nub $ (freeVarsTerm t1) ++ (freeVarsTerm t2)
freeVarsTerm (MonaTermCat t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermMinus t1 t2) = freeVarsTerm $ MonaTermPlus t1 t2
freeVarsTerm (MonaTermUp t) = freeVarsTerm t
freeVarsTerm (MonaTermRoot) = []


freeVarsAtom :: MonaAtom -> [Lo.Var]
freeVarsAtom (MonaAtomLe t1 t2) = nub $ (freeVarsTerm t1) ++ (freeVarsTerm t2)
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


varsDecl (MonaDeclPred _ _ f) = varsFormula f
varsDecl (MonaDeclVar0 vars) = vars
varsDecl (MonaDeclVar1 decl) = nub $ map (fst) decl
varsDecl (MonaDeclVar2 decl) = nub $ map (fst) decl
varsDecl (MonaDeclFormula f) = varsFormula f


varsFormula :: MonaFormula -> [Lo.Var]
varsFormula (MonaFormulaAtomic atom) = freeVarsAtom atom
varsFormula (MonaFormulaVar var) = [var]
varsFormula (MonaFormulaNeg f) = varsFormula f
varsFormula (MonaFormulaConj f1 f2) = nub $ (varsFormula f1) ++ (varsFormula f2)
varsFormula (MonaFormulaDisj f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaImpl f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaEquiv f1 f2) = varsFormula (MonaFormulaConj f1 f2)
varsFormula (MonaFormulaEx0 [var] f) = var:(varsFormula f)
varsFormula (MonaFormulaEx1 [var] f) = (fst var):(varsFormula f)
varsFormula (MonaFormulaEx2 [var] f) = (fst var):(varsFormula f)
varsFormula (MonaFormulaAll0 v f) = varsFormula (MonaFormulaEx0 v f)
varsFormula (MonaFormulaAll1 v f) = varsFormula (MonaFormulaEx1 v f)
varsFormula (MonaFormulaAll2 v f) = varsFormula (MonaFormulaEx2 v f)
varsFormula (MonaFormulaPredCall _ t) = concat $ map (freeVarsTerm) t
varsFormula t = error $ "varsFormula: unimplemented: " ++ show t  -- TODO: incomplete


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
