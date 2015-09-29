{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Arith.Context
    ( ArithType
    , ArithThry
    , ArithCtxt
    , ctxtArith
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition, newSpecification)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion

import HaskHOL.Lib.Nums.Context
import HaskHOL.Lib.Arith.Base

data ArithThry
type instance ArithThry == ArithThry = 'True

instance CtxtName ArithThry where
    ctxtName _ = "ArithCtxt"

type instance PolyTheory ArithType b = ArithCtxt b

type family ArithCtxt a :: Constraint where
    ArithCtxt a = (Typeable a, NumsCtxt a, ArithContext a ~ 'True)

type ArithType = ExtThry ArithThry NumsType

type family ArithContext a :: Bool where
    ArithContext BaseThry = 'False
    ArithContext (ExtThry a b) = ArithContext b || (a == ArithThry)

ctxtArith :: TheoryPath ArithType
ctxtArith = extendTheory ctxtNums $(thisModule') $
-- Stage 1
    do mapM_ parseAsInfix [ ("<", (12, "right"))
                          , ("<=", (12, "right"))
                          , (">", (12, "right"))
                          , (">=",(12,"right"))
                          , ("+",(16, "right"))
                          , ("-", (18, "left"))
                          , ("*", (20,"right"))
                          , ("EXP", (24, "left"))
                          , ("DIV", (22, "left"))
                          , ("MOD", (22, "left"))
                          ]
       mapM_ (newRecursiveDefinition recursionNUM)
         [ ("PRE", [str| (PRE 0 = 0) /\ 
                         (!n. PRE (SUC n) = n) |])
         , ("+", [str| (!n. 0 + n = n) /\ 
                       (!m n. (SUC m) + n = SUC(m + n)) |])
         , ("*", [str| (!n. 0 * n = 0) /\ 
                       (!m n. (SUC m) * n = (m * n) + n) |])
         , ("EXP", [str| (!m. m EXP 0 = 1) /\ 
                         (!m n. m EXP (SUC n) = m * (m EXP n)) |])
         , ("<=", [str| (!m. (m <= 0) <=> (m = 0)) /\
                        (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n)) |])
         , ("<", [str| (!m. (m < 0) <=> F) /\
                       (!m n. (m < SUC n) <=> (m = n) \/ (m < n)) |])
         , ("EVEN", [str| (EVEN 0 <=> T) /\
                          (!n. EVEN (SUC n) <=> ~(EVEN n)) |])
         , ("ODD", [str| (ODD 0 <=> F) /\
                         (!n. ODD (SUC n) <=> ~(ODD n)) |])
         , ("-", [str| (!m. m - 0 = m) /\
                       (!m n. m - (SUC n) = PRE(m - n)) |])
         , ("FACT", [str| (FACT 0 = 1) /\
                          (!n. FACT (SUC n) = (SUC n) * FACT(n)) |])
         ]
       mapM_ newDefinition
         [ (">=", [str| m >= n <=> n <= m |])
         , (">", [str| m > n <=> n < m |])
         , ("MAX", [str| !m n. MAX m n = if m <= n then n else m |])
         , ("MIN", [str| !m n. MIN m n = if m <= n then m else n |])
         ]
-- Stage 2
       parseAsBinder "minimal"
       void $ newSpecification ["DIV", "MOD"] =<<
                ruleREWRITE [thmSKOLEM] thmDIVMOD_EXIST_0
       void $ newDefinition 
                ("minimal", [str| (minimal) (P:num->bool) = 
                                  @n. P n /\ !m. m < n ==> ~(P m) |])
