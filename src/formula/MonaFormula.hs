{-|
Module      : MonaFormula
Description : Mona formula definitions
Author      : Ondrej Lengal, Vojtech Havlena 2018
License     : GPL-3
-}

module MonaFormula where

import AuxFunctions
import Data.List


--------------------------------------------------------------------------------------------------------------
-- Part with type definitions
--------------------------------------------------------------------------------------------------------------

-- terms in MONA expressions
data MonaTerm
  = MonaTermVar String
  | MonaTermConst Integer
  | MonaTermPlus MonaTerm MonaTerm
  | MonaTermCat MonaTerm MonaTerm
  | MonaTermUp MonaTerm
  | MonaTermMinus MonaTerm MonaTerm
  | MonaTermRoot
  | MonaTermEmpty
  | MonaTermDots
  | MonaTermBool MonaAtom
  | MonaTermBoolCall String [MonaTerm]
  | MonaTermPConst Integer
  | MonaTermUnion MonaTerm MonaTerm
  | MonaTermInter MonaTerm MonaTerm
  | MonaTermDifference MonaTerm MonaTerm
  | MonaTermSet [MonaTerm]
  deriving (Eq, Ord)


-- atomic formulae (atom) in MONA
data MonaAtom
  = MonaAtomLe MonaTerm MonaTerm
  | MonaAtomEq MonaTerm MonaTerm
  | MonaAtomNeq MonaTerm MonaTerm
  | MonaAtomLeq MonaTerm MonaTerm
  | MonaAtomGe MonaTerm MonaTerm
  | MonaAtomGeq MonaTerm MonaTerm
  | MonaAtomIn MonaTerm MonaTerm
  | MonaAtomNotIn MonaTerm MonaTerm
  | MonaAtomSub MonaTerm MonaTerm
  | MonaAtomSing MonaTerm
  | MonaAtomEps MonaTerm
  | MonaAtomTerm MonaTerm
  | MonaAtomIsEmpty MonaTerm
  | MonaAtomTrue
  | MonaAtomFalse
  deriving (Eq, Ord)


-- formulae in MONA
data MonaFormula
  = MonaFormulaAtomic MonaAtom
  | MonaFormulaVar String
  | MonaFormulaNeg MonaFormula
  | MonaFormulaDisj MonaFormula MonaFormula
  | MonaFormulaConj MonaFormula MonaFormula
  | MonaFormulaImpl MonaFormula MonaFormula
  | MonaFormulaEquiv MonaFormula MonaFormula
  | MonaFormulaEx0 [String] MonaFormula
  | MonaFormulaEx1 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaEx2 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaExGen String MonaFormula
  | MonaFormulaAll0 [String] MonaFormula
  | MonaFormulaAll1 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaAll2 [(String, Maybe MonaFormula)] MonaFormula
  | MonaFormulaPredCall String [MonaTerm]
  deriving (Eq, Ord)


-- MONA file declarations
data MonaDeclaration
  = MonaDeclFormula MonaFormula
  | MonaDeclVar0 [String]
  | MonaDeclVar1 [(String, Maybe MonaFormula)]
  | MonaDeclVar2 [(String, Maybe MonaFormula)]
  | MonaDeclAllpos String
  | MonaDeclLastpos String
  | MonaDeclDefWhere1 String MonaFormula
  | MonaDeclDefWhere2 String MonaFormula
  | MonaDeclMacro String [MonaMacroParam] MonaFormula
  | MonaDeclPred String [MonaMacroParam] MonaFormula
  | MonaDeclExport String MonaFormula
  | MonaDeclAssert MonaFormula
  | MonaDeclConst MonaAtom


-- representation of a MONA file
data MonaFile
  = MonaFile { mf_domain :: Maybe String
             , mf_decls :: [MonaDeclaration]
             }


-- macro parameters
data MonaMacroParam
  = MonaMacroParamVar0 [String]
  | MonaMacroParamVar1 [(String, Maybe MonaFormula)]
  | MonaMacroParamVar2 [(String, Maybe MonaFormula)]
  | MonaMacroParamUniv String



--------------------------------------------------------------------------------------------------------------
-- Part with instances
--------------------------------------------------------------------------------------------------------------

instance Show MonaTerm where
  show (MonaTermVar str) = str
  show (MonaTermRoot) = "root"
  show (MonaTermDots) = "..."
  show (MonaTermConst n) = show n
  show (MonaTermPlus t1 t2) = (pars $ show t1) ++ " + " ++ (show t2)
  show (MonaTermCat t1 t2) = (pars $ show t1) ++ " . " ++ (show t2)
  show (MonaTermMinus t1 t2) = (pars $ show t1) ++ " - " ++ (show t2)
  show (MonaTermUp t) = (pars $ show t) ++ "^"
  show (MonaTermBool atom) = show atom
  show (MonaTermBoolCall name terms) = name ++ "(" ++ (prArr "," terms) ++ ")"
  show (MonaTermPConst n) = "pconst(" ++ (show n) ++ ")"
  show (MonaTermEmpty) = "empty"
  show (MonaTermUnion t1 t2) = (pars $ show t1) ++ " union " ++ (pars $ show t2)
  show (MonaTermInter t1 t2) = (pars $ show t1) ++ " inter " ++ (pars $ show t2)
  show (MonaTermDifference t1 t2) = (pars $ show t1) ++ " \\ " ++ (pars $ show t2)
  show (MonaTermSet t) = "{" ++ (prArr "," t) ++  "}"


instance Show MonaAtom where
  show (MonaAtomLe t1 t2) = (show t1) ++ " < " ++ (show t2)
  show (MonaAtomLeq t1 t2) = (show t1) ++ " <= " ++ (show t2)
  show (MonaAtomEq t1 t2) = (show t1) ++ " = " ++ (show t2)
  show (MonaAtomNeq t1 t2) = (show t1) ++ " ~= " ++ (show t2)
  show (MonaAtomGe t1 t2) = (show t1) ++ " > " ++ (show t2)
  show (MonaAtomGeq t1 t2) = (show t1) ++ " >= " ++ (show t2)
  show (MonaAtomIn t1 t2) = pars ((show t1) ++ " in " ++ (show t2))
  show (MonaAtomNotIn t1 t2) = (show t1) ++ " notin " ++ (show t2)
  show (MonaAtomSub t1 t2) = (show t1) ++ " sub " ++ (show t2)
  show (MonaAtomTerm t) = show t
  show (MonaAtomSing t) = "sing( " ++ (show t) ++ " )"
  show (MonaAtomEps t) = "eps( " ++ (show t) ++ " )"
  show (MonaAtomIsEmpty t) = "empty(" ++ (show t) ++ ")"
  show MonaAtomTrue = "true"
  show MonaAtomFalse = "false"


instance Show MonaFormula where
  show (MonaFormulaAtomic atom) = show atom
  show (MonaFormulaVar str) = str
  show (MonaFormulaNeg phi) = "~(" ++ (show phi) ++ ")"
  show (MonaFormulaDisj f1 f2) = "((" ++ (show f1) ++ ") | (" ++ (show f2) ++ "))"
  show (MonaFormulaConj f1 f2) = "((" ++ (show f1) ++ ") & (" ++ (show f2) ++ "))"
  show (MonaFormulaImpl f1 f2) = "((" ++ (show f1) ++ ") => (" ++ (show f2) ++ "))"
  show (MonaFormulaEquiv f1 f2) = "((" ++ (show f1) ++ ") <=> (" ++ (show f2) ++ "))"
  show (MonaFormulaEx0 varList phi) = pars $
    "ex0 " ++ (commatize varList) ++ ": " ++ (show phi)
  show (MonaFormulaEx1 varWhereCl phi) = pars $
    "ex1 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaEx2 varWhereCl phi) = pars $
    "ex2 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaExGen var phi) = pars $
    "allGen " ++ var ++ ": " ++ (show phi)
  show (MonaFormulaAll0 varList phi) = pars $
    "all0 " ++ (commatize varList) ++ ": " ++ (show phi)
  show (MonaFormulaAll1 varWhereCl phi) = pars $
    "all1 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaAll2 varWhereCl phi) = pars $
    "all2 " ++ (showVarWhereClause varWhereCl) ++ ": " ++ (show phi)
  show (MonaFormulaPredCall name terms) = name ++ "(" ++ (prArr "," terms) ++ ")"


instance Show MonaDeclaration where
  show (MonaDeclFormula phi) = show phi
  show (MonaDeclVar0 varList) = "var0 " ++ (commatize varList)
  show (MonaDeclVar1 varWhereList) = "var1 " ++ showVarWhereClause varWhereList
  show (MonaDeclVar2 varWhereList) = "var2 " ++ showVarWhereClause varWhereList
  show (MonaDeclAllpos var) = "allpos " ++ var
  show (MonaDeclLastpos var) = "lastpos " ++ var
  show (MonaDeclDefWhere1 var phi) = "defaultwhere1(" ++ var ++ ") = " ++ (show phi)
  show (MonaDeclDefWhere2 var phi) = "defaultwhere2(" ++ var ++ ") = " ++ (show phi)
  show (MonaDeclMacro name params phi) = "macro " ++ name ++ "(" ++ (commatize $ map show params) ++ ") = " ++ (show phi)
  show (MonaDeclPred name params phi) = "pred " ++ name ++ "(" ++ (commatize $ map show params) ++ ") = " ++ (show phi)
  show (MonaDeclExport name phi) = "export(\"" ++ name ++ "\", " ++ (show phi) ++ ")"
  show (MonaDeclAssert phi) = "assert " ++ (show phi)
  show (MonaDeclConst atom) = "const "++ (show atom)


instance Show MonaFile where
  show f = (case mf_domain f of
              Nothing  -> ""
              Just dom -> dom ++ ";")
           ++ "\n" ++
           ((unlines . (map (\x -> (show x) ++ ";"))) (mf_decls f))


instance Show MonaMacroParam where
  show (MonaMacroParamVar0 varList) = "var0 " ++ (commatize varList)
  show (MonaMacroParamVar1 varWhereList) = "var1 " ++ (showVarWhereClause varWhereList)
  show (MonaMacroParamVar2 varWhereList) = "var2 " ++ (showVarWhereClause varWhereList)


showVarWhereClause :: [(String, Maybe MonaFormula)] -> String
showVarWhereClause = commatize . (map showVarWhere)
  where
    showVarWhere (var, whereCl) = var ++
      (case whereCl of
         Nothing  -> ""
         Just phi -> " where " ++ (show phi)
      )


-- put something inside parenthesis
pars :: String -> String
pars str = "(" ++ str ++ ")"


-- intercalate with commas
commatize :: [String] -> String
commatize list = intercalate ", " list
