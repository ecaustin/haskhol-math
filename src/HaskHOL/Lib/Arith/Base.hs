module HaskHOL.Lib.Arith.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification,
                                 newSpecification, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Arith.A

defPRE :: ArithACtxt thry => HOL cls thry HOLThm
defPRE = cacheProof "defPRE" ctxtArithA $ getRecursiveDefinition "PRE"

defADD :: ArithACtxt thry => HOL cls thry HOLThm
defADD = cacheProof "defADD" ctxtArithA $ getRecursiveDefinition "+"

defMULT :: ArithACtxt thry => HOL cls thry HOLThm
defMULT = cacheProof "defMULT" ctxtArithA $ getRecursiveDefinition "*"

defEXP :: ArithACtxt thry => HOL cls thry HOLThm
defEXP = cacheProof "defEXP" ctxtArithA $ getRecursiveDefinition "EXP"

defLE :: ArithACtxt thry => HOL cls thry HOLThm
defLE = cacheProof "defLE" ctxtArithA $ getRecursiveDefinition "<="

defLT :: ArithACtxt thry => HOL cls thry HOLThm
defLT = cacheProof "defLT" ctxtArithA $ getRecursiveDefinition "<"

defGE :: ArithACtxt thry => HOL cls thry HOLThm
defGE = cacheProof "defGE" ctxtArithA $ getDefinition ">="

defGT :: ArithACtxt thry => HOL cls thry HOLThm
defGT = cacheProof "defGT" ctxtArithA $ getDefinition ">"

defMAX :: ArithACtxt thry => HOL cls thry HOLThm
defMAX = cacheProof "defMAX" ctxtArithA $ getDefinition "MAX"

defMIN :: ArithACtxt thry => HOL cls thry HOLThm
defMIN = cacheProof "defMIN" ctxtArithA $ getDefinition "MIN"

defEVEN :: ArithACtxt thry => HOL cls thry HOLThm
defEVEN = cacheProof "defEVEN" ctxtArithA $ getRecursiveDefinition "EVEN"

defODD :: ArithACtxt thry => HOL cls thry HOLThm
defODD = cacheProof "defODD" ctxtArithA $ getRecursiveDefinition "ODD"

defSUB :: ArithACtxt thry => HOL cls thry HOLThm
defSUB = cacheProof "defSUB" ctxtArithA $ getRecursiveDefinition "-"

defFACT :: ArithACtxt thry => HOL cls thry HOLThm
defFACT = cacheProof "defFACT" ctxtArithA $ getRecursiveDefinition "FACT"


thmADD_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_0 = cacheProof "thmADD_0" ctxtArithA $
    prove "!m. m + 0 = m" $
      tacINDUCT `_THEN` tacASM_REWRITE [defADD]

thmADD_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SUC = cacheProof "thmADD_SUC" ctxtArithA $
    prove "!m n. m + (SUC n) = SUC (m + n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [defADD]

thmLE_SUC_LT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_SUC_LT = cacheProof "thmLE_SUC_LT" ctxtArithA $
    prove "!m n. (SUC m <= n) <=> (m < n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defLE, defLT, thmNOT_SUC, thmSUC_INJ]

thmLT_SUC_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_SUC_LE = cacheProof "thmLT_SUC_LE" ctxtArithA $
    prove "!m n. (m < SUC n) <=> (m <= n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` tacONCE_REWRITE [defLT, defLE] `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacREWRITE [defLT]

thmLE_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_0 = cacheProof "thmLE_0" ctxtArithA $
    prove "!n. 0 <= n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defLE]

wfNUM' :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
wfNUM' = cacheProof "wfNUM'" ctxtArithA $
    prove "!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n" $
      tacGEN `_THEN` 
      tacMP (ruleSPEC "\\n. !m. m < n ==> P m" inductionNUM) `_THEN`
      tacREWRITE [defLT, thmBETA] `_THEN` tacMESON [defLT]

thmSUB_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_0 = cacheProof "thmSUB_0" ctxtArithA $
    prove [str| !m. (0 - m = 0) /\ (m - 0 = m) |] $
      tacREWRITE [defSUB] `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defSUB, defPRE]

thmSUB_PRESUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_PRESUC = cacheProof "thmSUB_PRESUC" ctxtArithA $
    prove "!m n. PRE(SUC m - n) = m - n" $
      tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE [defSUB, defPRE]

thmLE_REFL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_REFL = cacheProof "thmLE_REFL" ctxtArithA $
    prove "!n. n <= n" $ tacINDUCT `_THEN` tacREWRITE [defLE]

thmNOT_EVEN :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmNOT_EVEN = cacheProof "thmNOT_EVEN" ctxtArithA $
    prove "!n. ~(EVEN n) <=> ODD n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defEVEN, defODD]

thmNOT_ODD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmNOT_ODD = cacheProof "thmNOT_ODD" ctxtArithA $
    prove "!n. ~(ODD n) <=> EVEN n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defEVEN, defODD]

thmADD_CLAUSES :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_CLAUSES = cacheProof "thmADD_CLAUSES" ctxtArithA $
    prove [str| (!n. 0 + n = n) /\
                (!m. m + 0 = m) /\
                (!m n. (SUC m) + n = SUC(m + n)) /\
                (!m n. m + (SUC n) = SUC(m + n)) |] $
      tacREWRITE [defADD, thmADD_0, thmADD_SUC]
      
thmLE_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_SUC = cacheProof "thmLE_SUC" ctxtArithA $
    prove "!m n. (SUC m <= SUC n) <=> (m <= n)" $
      tacREWRITE [thmLE_SUC_LT, thmLT_SUC_LE]

thmLT_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_SUC = cacheProof "thmLT_SUC" ctxtArithA $
    prove "!m n. (SUC m < SUC n) <=> (m < n)" $
      tacREWRITE [thmLT_SUC_LE, thmLE_SUC_LT]

wopNUM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
wopNUM = cacheProof "wopNUM" ctxtArithA $
    prove [str| !P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m)) |] $
      tacGEN `_THEN` tacEQ `_THENL` [_ALL, tacMESON_NIL] `_THEN`
      tacCONV convCONTRAPOS `_THEN` tacREWRITE [thmNOT_EXISTS] `_THEN`
      tacDISCH `_THEN` tacMATCH_MP wfNUM' `_THEN` tacASM_MESON_NIL

thmSUB_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_SUC = cacheProof "thmSUB_SUC" ctxtArithA $
    prove "!m n. SUC m - SUC n = m - n" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [defSUB, defPRE, thmSUB_PRESUC]

thmEVEN_OR_ODD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEVEN_OR_ODD = cacheProof "thmEVEN_OR_ODD" ctxtArithA $
    prove [str| !n. EVEN n \/ ODD n |] $
      tacINDUCT `_THEN` 
      tacREWRITE [defEVEN, defODD, thmNOT_EVEN, thmNOT_ODD] `_THEN`
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacASM_REWRITE_NIL

thmEVEN_AND_ODD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEVEN_AND_ODD = cacheProof "thmEVEN_AND_ODD" ctxtArithA $
    prove [str| !n. ~(EVEN n /\ ODD n) |] $
      tacREWRITE [ruleGSYM thmNOT_EVEN, ruleITAUT [str| ~(p /\ ~p) |]]

thmLET_CASES :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLET_CASES = cacheProof "thmLET_CASES" ctxtArithA $
    prove [str| !m n. m <= n \/ n < m |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC_LT, thmLT_SUC_LE, thmLE_0]

thmEQ_IMP_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEQ_IMP_LE = cacheProof "thmEQ_IMP_LE" ctxtArithA $
    prove "!m n. (m = n) ==> m <= n" $
      _REPEAT tacSTRIP `_THEN` tacASM_REWRITE [thmLE_REFL]

thmADD_SYM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SYM = cacheProof "thmADD_SYM" ctxtArithA $
    prove "!m n. m + n = n + m" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmEQ_ADD_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL = cacheProof "thmEQ_ADD_LCANCEL" ctxtArithA $
    prove "!m n p. (m + n = m + p) <=> (n = p)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmBIT0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmBIT0 = cacheProof "thmBIT0" ctxtArithA $
    prove "!n. BIT0 n = n + n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defBIT0, thmADD_CLAUSES]

thmMULT_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_0 = cacheProof "thmMULT_0" ctxtArithA $
    prove "!m. m * 0 = 0" $
      tacINDUCT `_THEN` tacASM_REWRITE [defMULT, thmADD_CLAUSES]

thmADD_ASSOC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_ASSOC = cacheProof "thmADD_ASSOC" ctxtArithA $
    prove "!m n p. m + (n + p) = (m + n) + p" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmADD_EQ_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_EQ_0 = cacheProof "thmADD_EQ_0" ctxtArithA $
    prove [str| !m n. (m + n = 0) <=> (m = 0) /\ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmNOT_SUC]

thmLT_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_0 = cacheProof "thmLT_0" ctxtArithA $
    prove "!n. 0 < SUC n" $
      tacREWRITE [thmLT_SUC_LE, thmLE_0]

thmLT_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_ADD = cacheProof "thmLT_ADD" ctxtArithA $
    prove "!m n. (m < m + n) <=> (0 < n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmLT_SUC]

thmADD_SUB :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SUB = cacheProof "thmADD_SUB" ctxtArithA $
    prove "!m n. (m + n) - n = m" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_SUC, thmSUB_0]

thmLT_REFL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_REFL = cacheProof "thmLT_REFL" ctxtArithA $
    prove "!n. ~(n < n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmLT_SUC] `_THEN` 
      tacREWRITE [defLT]

thmSUB_EQ_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_EQ_0 = cacheProof "thmSUB_EQ_0" ctxtArithA $
    prove "!m n. (m - n = 0) <=> m <= n" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmSUB_SUC, thmLE_SUC, thmSUB_0] `_THEN`
      tacREWRITE [defLE, thmLE_0]

thmLE_CASES :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_CASES = cacheProof "thmLE_CASES" ctxtArithA $
    prove [str| !m n. m <= n \/ n <= m |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_0, thmLE_SUC]

thmLE_ANTISYM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ANTISYM = cacheProof "thmLE_ANTISYM" ctxtArithA $
     prove [str| !m n. (m <= n /\ n <= m) <=> (m = n) |] $
       _REPEAT tacINDUCT `_THEN` 
       tacASM_REWRITE [thmLE_SUC, thmSUC_INJ] `_THEN`
       tacREWRITE [defLE, thmNOT_SUC, ruleGSYM thmNOT_SUC]

thmLET_ANTISYM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLET_ANTISYM = cacheProof "thmLET_ANTISYM" ctxtArithA $
    prove [str| !m n. ~(m <= n /\ n < m) |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [defLE, defLT, thmNOT_SUC]

thmEVEN_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEVEN_ADD = cacheProof "thmEVEN_ADD" ctxtArithA $
    prove "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [defEVEN, thmADD_CLAUSES] `_THEN`
      tacX_GEN "p:num" `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "n:num" thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "p:num" thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmLE_TRANS :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_TRANS = cacheProof "thmLE_TRANS" ctxtArithA $
    prove [str| !m n p. m <= n /\ n <= p ==> m <= p |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLE_0] `_THEN`
      tacREWRITE [defLE, thmNOT_SUC]
    
thmSUB_REFL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_REFL = cacheProof "thmSUB_REFL" ctxtArithA $
    prove "!n. n - n = 0" $ 
      tacINDUCT `_THEN` tacASM_REWRITE [thmSUB_SUC, thmSUB_0]

thmLE_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ADD = cacheProof "thmLE_ADD" ctxtArithA $
    prove "!m n. m <= m + n" $
      tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [defLE, thmADD_CLAUSES, thmLE_REFL]

thmLTE_CASES :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLTE_CASES = cacheProof "thmLTE_CASES" ctxtArithA $
    prove [str| !m n. m < n \/ n <= m |] $
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacMATCH_ACCEPT thmLET_CASES

thmSUB_ADD_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmSUB_ADD_LCANCEL = cacheProof "thmSUB_ADD_LCANCEL" ctxtArithA $
    prove "!m n p. (m + n) - (m + p) = n - p" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_0, thmSUB_SUC]

thmBIT0_THM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmBIT0_THM = cacheProof "thmBIT0_THM" ctxtArithA $
    prove "!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n" $
      tacREWRITE [defNUMERAL, thmBIT0]

thmBIT1 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmBIT1 = cacheProof "thmBIT1" ctxtArithA $
    prove "!n. BIT1 n = SUC(n + n)" $
      tacREWRITE [defBIT1, thmBIT0]

thmMULT_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_SUC = cacheProof "thmMULT_SUC" ctxtArithA $
    prove "!m n. m * (SUC n) = m + (m * n)" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defMULT, thmADD_CLAUSES, thmADD_ASSOC]

thmNOT_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmNOT_LE = cacheProof "thmNOT_LE" ctxtArithA $
    prove "!m n. ~(m <= n) <=> (n < m)" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ defLE, defLT, thmNOT_SUC
                 , ruleGSYM thmNOT_SUC, thmLE_0 ] `_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]


thmNOT_LT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmNOT_LT = cacheProof "thmNOT_LT" ctxtArithA $
    prove "!m n. ~(m < n) <=> n <= m" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [defLE, defLT, thmNOT_SUC, ruleGSYM thmNOT_SUC, thmLE_0]`_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]

thmLE_EXISTS :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_EXISTS = cacheProof "thmLE_EXISTS" ctxtArithA $
    prove "!m n. (m <= n) <=> (?d. n = m + d)" $
      tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE [defLE] `_THENL`
      [ tacREWRITE [ruleCONV (convLAND convSYM) =<< 
                      ruleSPEC_ALL thmADD_EQ_0] `_THEN`
        tacREWRITE [thmRIGHT_EXISTS_AND, thmEXISTS_REFL]
      , tacEQ `_THENL`
        [ _DISCH_THEN (_DISJ_CASES_THEN2 tacSUBST1 tacMP) `_THENL`
          [ tacEXISTS "0" `_THEN` tacREWRITE [thmADD_CLAUSES]
          , _DISCH_THEN (_X_CHOOSE_THEN "d:num" tacSUBST1) `_THEN`
            tacEXISTS "SUC d" `_THEN` tacREWRITE [thmADD_CLAUSES]
          ]
        , tacONCE_REWRITE [thmLEFT_IMP_EXISTS] `_THEN`
          tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmSUC_INJ] `_THEN`
          _DISCH_THEN tacSUBST1 `_THEN` tacREWRITE_NIL `_THEN` 
          tacDISJ2 `_THEN`
          tacREWRITE [thmEQ_ADD_LCANCEL, ruleGSYM thmEXISTS_REFL]
        ]
      ]

thmLT_EXISTS :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_EXISTS = cacheProof "thmLT_EXISTS" ctxtArithA $
    prove "!m n. (m < n) <=> (?d. n = m + SUC d)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacREWRITE [defLT, thmADD_CLAUSES, ruleGSYM thmNOT_SUC] `_THEN`
      tacASM_REWRITE [thmSUC_INJ] `_THEN` tacEQ `_THENL`
      [ _DISCH_THEN (_DISJ_CASES_THEN2 tacSUBST1 tacMP) `_THENL`
        [ tacEXISTS "0" `_THEN` tacREWRITE [thmADD_CLAUSES]
        , _DISCH_THEN (_X_CHOOSE_THEN "d:num" tacSUBST1) `_THEN`
          tacEXISTS "SUC d" `_THEN` tacREWRITE [thmADD_CLAUSES]
        ]
      , tacONCE_REWRITE [thmLEFT_IMP_EXISTS] `_THEN`
        tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmSUC_INJ] `_THEN`
        _DISCH_THEN tacSUBST1 `_THEN` tacREWRITE_NIL `_THEN` 
        tacDISJ2 `_THEN` tacREWRITE [ thmSUC_INJ, thmEQ_ADD_LCANCEL
                                    , ruleGSYM thmEXISTS_REFL ]
      ]

thmLT_ADDR :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_ADDR = cacheProof "thmLT_ADDR" ctxtArithA $
    prove "!m n. (n < m + n) <=> (0 < m)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLT_ADD

thmADD_SUB2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SUB2 = cacheProof "thmADD_SUB2" ctxtArithA $
    prove "!m n. (m + n) - m = n" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUB

thmLTE_ANTISYM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLTE_ANTISYM = cacheProof "thmLTE_ANTISYM" ctxtArithA $
    prove [str| !m n. ~(m < n /\ n <= m) |] $
      tacONCE_REWRITE [thmCONJ_SYM] `_THEN` tacREWRITE [thmLET_ANTISYM]

thmLE_LT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_LT = cacheProof "thmLE_LT" ctxtArithA $
    prove [str| !m n. (m <= n) <=> (m < n) \/ (m = n) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmLE_SUC, thmLT_SUC
                     , thmSUC_INJ, thmLE_0, thmLT_0 ] `_THEN`
      tacREWRITE [defLE, defLT]

thmARITH_ZERO :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_ZERO = cacheProof "thmARITH_ZERO" ctxtArithA $
    prove [str| (NUMERAL 0 = 0) /\ (BIT0 _0 = _0) |] $
      tacREWRITE [defNUMERAL, thmBIT0, ruleDENUMERAL thmADD_CLAUSES]

thmADD_AC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_AC = cacheProof "thmADD_AC" ctxtArithA $
    prove [str| (m + n = n + m) /\
                ((m + n) + p = m + (n + p)) /\
                (m + (n + p) = n + (m + p)) |] $
      tacMESON [thmADD_ASSOC, thmADD_SYM]

thmODD_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmODD_ADD = cacheProof "thmODD_ADD" ctxtArithA $
    prove "!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)" $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [ruleGSYM thmNOT_EVEN, thmEVEN_ADD] `_THEN`
      tacCONV (Conv ruleITAUT)

thmEQ_ADD_RCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEQ_ADD_RCANCEL = cacheProof "thmEQ_ADD_RCANCEL" ctxtArithA $
    prove "!m n p. (m + p = n + p) <=> (m = n)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmEQ_ADD_LCANCEL

thmLTE_TRANS :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLTE_TRANS = cacheProof "thmLTE_TRANS" ctxtArithA $
    prove [str| !m n p. m < n /\ n <= p ==> m < p |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC, thmLT_0] `_THEN`
      tacREWRITE [defLT, defLE, thmNOT_SUC]

thmADD_SUBR2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SUBR2 = cacheProof "thmADD_SUBR2" ctxtArithA $
    prove "!m n. m - (m + n) = 0" $
      tacREWRITE [thmSUB_EQ_0, thmLE_ADD]

thmEQ_ADD_LCANCEL_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL_0 = cacheProof "thmEQ_ADD_LCANCEL_0" ctxtArithA $
    prove "!m n. (m + n = m) <=> (n = 0)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmLE_ADDR :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ADDR = cacheProof "thmLE_ADDR" ctxtArithA $
    prove "!m n. n <= m + n" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLE_ADD

thmBIT1_THM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmBIT1_THM = cacheProof "thmBIT1_THM" ctxtArithA $
    prove "!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)" $
      tacREWRITE [defNUMERAL, thmBIT1]

thmLT_ADD_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_ADD_LCANCEL = cacheProof "thmLT_ADD_LCANCEL" ctxtArithA $
    prove "!m n p. (m + n) < (m + p) <=> n < p" $
      tacREWRITE [ thmLT_EXISTS, ruleGSYM thmADD_ASSOC
                 , thmEQ_ADD_LCANCEL, thmSUC_INJ ]

thmLE_ADD_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ADD_LCANCEL = cacheProof "thmLE_ADD_LCANCEL" ctxtArithA $
    prove "!m n p. (m + n) <= (m + p) <=> n <= p" $
      tacREWRITE [thmLE_EXISTS, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmARITH_SUC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_SUC = cacheProof "thmARITH_SUC" ctxtArithA $
    prove [str| (!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
                (SUC _0 = BIT1 _0) /\
                (!n. SUC (BIT0 n) = BIT1 n) /\
                (!n. SUC (BIT1 n) = BIT0 (SUC n)) |] $
      tacREWRITE [defNUMERAL, thmBIT0, thmBIT1, ruleDENUMERAL thmADD_CLAUSES]

thmARITH_PRE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_PRE = cacheProof "thmARITH_PRE" ctxtArithA $
    prove [str| (!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
                (PRE _0 = _0) /\
                (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
                (!n. PRE(BIT1 n) = BIT0 n) |] $
      tacREWRITE [defNUMERAL, thmBIT1, thmBIT0, ruleDENUMERAL defPRE] `_THEN` 
      tacINDUCT `_THEN` tacREWRITE [ defNUMERAL, ruleDENUMERAL defPRE
                                   , ruleDENUMERAL thmADD_CLAUSES
                                   , ruleDENUMERAL thmNOT_SUC, thmARITH_ZERO ]

thmARITH_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_ADD = cacheProof "thmARITH_ADD" ctxtArithA $
    prove [str| (!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\
                (_0 + _0 = _0) /\
                (!n. _0 + BIT0 n = BIT0 n) /\
                (!n. _0 + BIT1 n = BIT1 n) /\
                (!n. BIT0 n + _0 = BIT0 n) /\
                (!n. BIT1 n + _0 = BIT1 n) /\
                (!m n. BIT0 m + BIT0 n = BIT0 (m + n)) /\
                (!m n. BIT0 m + BIT1 n = BIT1 (m + n)) /\
                (!m n. BIT1 m + BIT0 n = BIT1 (m + n)) /\
                (!m n. BIT1 m + BIT1 n = BIT0 (SUC(m + n))) |] $
      tacPURE_REWRITE [ defNUMERAL, thmBIT0, thmBIT1
                      , ruleDENUMERAL thmADD_CLAUSES, thmSUC_INJ ] `_THEN`
      tacREWRITE [thmADD_AC]

thmARITH_EVEN :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_EVEN = cacheProof "thmARITH_EVEN" ctxtArithA $
    prove [str| (!n. EVEN(NUMERAL n) <=> EVEN n) /\
                (EVEN _0 <=> T) /\
                (!n. EVEN(BIT0 n) <=> T) /\
               (!n. EVEN(BIT1 n) <=> F) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0, ruleDENUMERAL defEVEN
                 , thmEVEN_ADD ]

thmARITH_ODD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_ODD = cacheProof "thmARITH_ODD" ctxtArithA $
    prove [str| (!n. ODD(NUMERAL n) <=> ODD n) /\
                (ODD _0 <=> F) /\
                (!n. ODD(BIT0 n) <=> F) /\
                (!n. ODD(BIT1 n) <=> T) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                 , ruleDENUMERAL defODD, thmODD_ADD ]

thmLE_ADD2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ADD2 = cacheProof "thmLE_ADD2" ctxtArithA $
    prove [str| !m n p q. m <= p /\ n <= q ==> m + n <= p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN 
        (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
         (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a + b" `_THEN` tacASM_REWRITE [thmADD_AC]

thmADD_SUBR :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD_SUBR = cacheProof "thmADD_SUBR" ctxtArithA $
    prove "!m n. n - (m + n) = 0" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUBR2

thmLT_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_LE = cacheProof "thmLT_LE" ctxtArithA $
    prove [str| !m n. (m < n) <=> (m <= n) /\ ~(m = n) |] $
      tacREWRITE [thmLE_LT] `_THEN` _REPEAT tacGEN `_THEN` tacEQ `_THENL`
      [ tacDISCH `_THEN` tacASM_REWRITE_NIL `_THEN` 
        _DISCH_THEN tacSUBST_ALL `_THEN` _POP_ASSUM tacMP `_THEN`
        tacREWRITE [thmLT_REFL]
      , _DISCH_THEN (_CONJUNCTS_THEN2 tacSTRIP_ASSUME tacMP) `_THEN`
        tacASM_REWRITE_NIL
      ]

thmLET_ADD2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLET_ADD2 = cacheProof "thmLET_ADD2" ctxtArithA $
    prove [str| !m n p q. m <= p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS, thmLT_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
                     (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a + b" `_THEN` 
      tacASM_REWRITE [thmSUC_INJ, thmADD_CLAUSES, thmADD_AC]

thmADD1 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmADD1 = cacheProof "thmADD1" ctxtArithA $
    prove "!m. SUC m = m + 1" $
      tacREWRITE [thmBIT1_THM, thmADD_CLAUSES]

thmMULT_CLAUSES :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_CLAUSES = cacheProof "thmMULT_CLAUSES" ctxtArithA $
    prove [str| (!n. 0 * n = 0) /\
                (!m. m * 0 = 0) /\
                (!n. 1 * n = n) /\
                (!m. m * 1 = m) /\
                (!m n. (SUC m) * n = (m * n) + n) /\
                (!m n. m * (SUC n) = m + (m * n)) |] $
      tacREWRITE [ thmBIT1_THM, defMULT, thmMULT_0
                 , thmMULT_SUC, thmADD_CLAUSES ]

thmLT_IMP_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_IMP_LE = cacheProof "thmLT_IMP_LE" ctxtArithA $
    prove "!m n. m < n ==> m <= n" $
      tacREWRITE [thmLT_LE] `_THEN` _REPEAT tacSTRIP `_THEN` 
      tacASM_REWRITE_NIL

thmLE_ADD_RCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_ADD_RCANCEL = cacheProof "thmLE_ADD_RCANCEL" ctxtArithA $
    prove "!m n p. (m + p) <= (n + p) <=> (m <= n)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmLE_ADD_LCANCEL

thmLTE_ADD2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLTE_ADD2 = cacheProof "thmLTE_ADD2" ctxtArithA $
    prove [str| !m n p q. m < p /\ n <= q ==> m + n < p + q |] $
      tacONCE_REWRITE [thmADD_SYM, thmCONJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLET_ADD2

thmMULT_SYM :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_SYM = cacheProof "thmMULT_SYM" ctxtArithA .
    prove "!m n. m * n = n * m" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmMULT_CLAUSES
                     , ruleEQT_INTRO =<< ruleSPEC_ALL thmADD_SYM ]

thmLEFT_ADD_DISTRIB :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLEFT_ADD_DISTRIB = cacheProof "thmLEFT_ADD_DISTRIB" ctxtArithA .
    prove "!m n p. m * (n + p) = (m * n) + (m * p)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defADD, thmMULT_CLAUSES, thmADD_ASSOC]

thmLE_MULT_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_MULT_LCANCEL = cacheProof "thmLE_MULT_LCANCEL" ctxtArithA $
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [str| !m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                        , thmLE_REFL, thmLE_0, thmNOT_SUC ] `_THEN`
         tacREWRITE [thmLE_SUC] `_THEN`
         tacREWRITE [defLE, thmLE_ADD_LCANCEL, ruleGSYM thmADD_ASSOC] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmLT_MULT_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_MULT_LCANCEL = cacheProof "thmLT_MULT_LCANCEL" ctxtArithA $
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [str| !m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                        , thmLT_REFL, thmLT_0, thmNOT_SUC] `_THEN`
         tacREWRITE [thmLT_SUC] `_THEN`
         tacREWRITE [defLT, thmLT_ADD_LCANCEL, ruleGSYM thmADD_ASSOC] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmMULT_EQ_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_EQ_0 = cacheProof "thmMULT_EQ_0" ctxtArithA .
    prove [str| !m n. (m * n = 0) <=> (m = 0) \/ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES, thmNOT_SUC]

thmEQ_MULT_LCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEQ_MULT_LCANCEL = cacheProof "thmEQ_MULT_LCANCEL" ctxtArithA $
    prove [str| !m n p. (m * n = m * p) <=> (m = 0) \/ (n = p) |] $
      tacINDUCT `_THEN` tacREWRITE [thmMULT_CLAUSES, thmNOT_SUC] `_THEN`
      _REPEAT tacINDUCT `_THEN`
      tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                     , ruleGSYM thmNOT_SUC, thmNOT_SUC ] `_THEN`
      tacASM_REWRITE [thmSUC_INJ, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmEVEN_MULT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEVEN_MULT = cacheProof "thmEVEN_MULT" ctxtArithA .
    prove [str| !m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n) |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [thmMULT_CLAUSES, thmEVEN_ADD, defEVEN] `_THEN`
      tacX_GEN "p:num" `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "n:num" thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "p:num" thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmEXP_EQ_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEXP_EQ_0 = cacheProof "thmEXP_EQ_0" ctxtArithA .
    prove [str| !m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmBIT1_THM, thmNOT_SUC, defEXP
                     , thmMULT_CLAUSES, thmADD_CLAUSES, thmADD_EQ_0 ]

thmLT_ADD2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLT_ADD2 = cacheProof "thmLT_ADD2" ctxtArithA .
    prove [str| !m n p q. m < p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacSTRIP `_THEN` tacMATCH_MP thmLTE_ADD2 `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacMATCH_MP thmLT_IMP_LE `_THEN`
      tacASM_REWRITE_NIL

thmRIGHT_ADD_DISTRIB :: (BasicConvs thry, ArithACtxt thry) 
                     => HOL cls thry HOLThm
thmRIGHT_ADD_DISTRIB = cacheProof "thmRIGHT_ADD_DISTRIB" ctxtArithA .
    prove "!m n p. (m + n) * p = (m * p) + (n * p)" $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_ADD_DISTRIB

thmLEFT_SUB_DISTRIB :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLEFT_SUB_DISTRIB = cacheProof "thmLEFT_SUB_DISTRIB" ctxtArithA .
    prove "!m n p. m * (n - p) = m * n - m * p" $
      _REPEAT tacGEN `_THEN` tacCONV convSYM `_THEN`
      tacDISJ_CASES (ruleSPECL ["n:num", "p:num"] thmLE_CASES) `_THENL`
      [ _FIRST_ASSUM 
          (\ th -> tacREWRITE [ruleREWRITE [ruleGSYM thmSUB_EQ_0] th])`_THEN`
        tacASM_REWRITE [thmMULT_CLAUSES, thmSUB_EQ_0, thmLE_MULT_LCANCEL]
      , _POP_ASSUM (_CHOOSE_THEN tacSUBST1 . ruleREWRITE [thmLE_EXISTS]) `_THEN`
        tacREWRITE [thmLEFT_ADD_DISTRIB] `_THEN`
        tacREWRITE [ruleONCE_REWRITE [thmADD_SYM] thmADD_SUB]
      ]

thmEVEN_DOUBLE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEVEN_DOUBLE = cacheProof "thmEVEN_DOUBLE" ctxtArithA .
    prove "!n. EVEN(2 * n)" $
      tacGEN `_THEN` tacREWRITE [thmEVEN_MULT] `_THEN` tacDISJ1 `_THEN`
      tacPURE_REWRITE [thmBIT0_THM, thmBIT1_THM] `_THEN` 
      tacREWRITE [defEVEN, thmEVEN_ADD]

thmLE_MULT_RCANCEL :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_MULT_RCANCEL = cacheProof "thmLE_MULT_RCANCEL" ctxtArithA .
    prove [str| !m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0) |] $
      tacONCE_REWRITE [thmMULT_SYM, thmDISJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLE_MULT_LCANCEL

thmDIVMOD_EXIST :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmDIVMOD_EXIST = cacheProof "thmDIVMOD_EXIST" ctxtArithA .
    prove [str| !m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\ r < n |] $
      _REPEAT tacSTRIP `_THEN` 
      tacMP (ruleSPEC [str| \r. ?q. m = q * n + r |] wopNUM) `_THEN`
      tacBETA `_THEN` _DISCH_THEN (tacMP . liftM fst . ruleEQ_IMP) `_THEN`
      tacREWRITE [thmLEFT_IMP_EXISTS] `_THEN`
      _DISCH_THEN (tacMP . ruleSPECL ["m:num", "0"]) `_THEN`
      tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
      _DISCH_THEN (_X_CHOOSE_THEN "r:num" tacMP) `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "q:num") tacMP) `_THEN`
      _DISCH_THEN (\ th -> _MAP_EVERY tacEXISTS ["q:num", "r:num"] `_THEN` 
                           tacMP th) `_THEN`
      tacCONV convCONTRAPOS `_THEN` tacASM_REWRITE [thmNOT_LT] `_THEN`
      _DISCH_THEN (_X_CHOOSE_THEN "d:num" tacSUBST_ALL . 
                   ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacREWRITE [thmNOT_FORALL] `_THEN` tacEXISTS "d:num" `_THEN`
      tacREWRITE [thmNOT_IMP, thmRIGHT_AND_EXISTS] `_THEN`
      tacEXISTS "q + 1" `_THEN` tacREWRITE [thmRIGHT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmMULT_CLAUSES, thmADD_ASSOC, thmLT_ADDR] `_THEN`
      tacASM_REWRITE [ruleGSYM thmNOT_LE, defLE]

thmMULT_2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_2 = cacheProof "thmMULT_2" ctxtArithA .
    prove "!n. 2 * n = n + n" $
      tacGEN `_THEN` 
      tacREWRITE [thmBIT0_THM, thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmARITH_MULT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_MULT = cacheProof "thmARITH_MULT" ctxtArithA $
    prove [str| (!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\
                (_0 * _0 = _0) /\
                (!n. _0 * BIT0 n = _0) /\
                (!n. _0 * BIT1 n = _0) /\
                (!n. BIT0 n * _0 = _0) /\
                (!n. BIT1 n * _0 = _0) /\
                (!m n. BIT0 m * BIT0 n = BIT0 (BIT0 (m * n))) /\
                (!m n. BIT0 m * BIT1 n = BIT0 m + BIT0 (BIT0 (m * n))) /\
                (!m n. BIT1 m * BIT0 n = BIT0 n + BIT0 (BIT0 (m * n))) /\
                (!m n. BIT1 m * BIT1 n = 
                       BIT1 m + BIT0 n + BIT0 (BIT0 (m * n))) |] $
      tacPURE_REWRITE [ defNUMERAL, thmBIT0, thmBIT1
                      , ruleDENUMERAL thmMULT_CLAUSES
                      , ruleDENUMERAL thmADD_CLAUSES, thmSUC_INJ ] `_THEN`
      tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB, thmADD_AC]

thmMULT_ASSOC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_ASSOC = cacheProof "thmMULT_ASSOC" ctxtArithA .
    prove "!m n p. m * (n * p) = (m * n) * p" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmLE_MULT2 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmLE_MULT2 = cacheProof "thmLE_MULT2" ctxtArithA .
    prove [str| !m n p q. m <= n /\ p <= q ==> m * p <= n * q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
                     (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a * p + m * b + a * b" `_THEN`
      tacASM_REWRITE [thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB, thmADD_ASSOC]

thmRIGHT_SUB_DISTRIB :: (BasicConvs thry, ArithACtxt thry) 
                     => HOL cls thry HOLThm
thmRIGHT_SUB_DISTRIB = cacheProof "thmRIGHT_SUB_DISTRIB" ctxtArithA .
    prove "!m n p. (m - n) * p = m * p - n * p" $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_SUB_DISTRIB

thmARITH_LE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_LE = cacheProof "thmARITH_LE" ctxtArithA $
    do tm <- toHTm "EVEN"
       prove [str| (!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\
                   ((_0 <= _0) <=> T) /\
                   (!n. (BIT0 n <= _0) <=> n <= _0) /\
                   (!n. (BIT1 n <= _0) <=> F) /\
                   (!n. (_0 <= BIT0 n) <=> T) /\
                   (!n. (_0 <= BIT1 n) <=> T) /\
                   (!m n. (BIT0 m <= BIT0 n) <=> m <= n) /\
                   (!m n. (BIT0 m <= BIT1 n) <=> m <= n) /\
                   (!m n. (BIT1 m <= BIT0 n) <=> m < n) /\
                   (!m n. (BIT1 m <= BIT1 n) <=> m <= n) |] $
         tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                    , ruleDENUMERAL thmNOT_SUC
                    , ruleDENUMERAL =<< ruleGSYM thmNOT_SUC, thmSUC_INJ] `_THEN`
         tacREWRITE [ruleDENUMERAL thmLE_0] `_THEN` 
         tacREWRITE [ruleDENUMERAL defLE, ruleGSYM thmMULT_2] `_THEN`
         tacREWRITE [ thmLE_MULT_LCANCEL, thmSUC_INJ, ruleDENUMERAL thmMULT_EQ_0
                    , ruleDENUMERAL thmNOT_SUC ] `_THEN`
         tacREWRITE [ruleDENUMERAL thmNOT_SUC] `_THEN` 
         tacREWRITE [thmLE_SUC_LT] `_THEN`
         tacREWRITE [thmLT_MULT_LCANCEL] `_THEN`
         _SUBGOAL_THEN "2 = SUC 1" (\ th -> tacREWRITE [th]) `_THENL`
         [ tacREWRITE [ defNUMERAL, thmBIT0, thmBIT1
                      , ruleDENUMERAL thmADD_CLAUSES ]
         , tacREWRITE [ ruleDENUMERAL thmNOT_SUC
                      , thmNOT_SUC, thmEQ_MULT_LCANCEL ] `_THEN`
           tacREWRITE [ruleONCE_REWRITE [thmDISJ_SYM] thmLE_LT] `_THEN`
           _MAP_EVERY tacX_GEN ["m:num", "n:num"] `_THEN`
           _SUBGOAL_THEN "~(SUC 1 * m = SUC (SUC 1 * n))" 
             (\ th -> tacREWRITE [th]) `_THEN`
           _DISCH_THEN (tacMP <#< ruleAP_TERM tm) `_THEN`
           tacREWRITE [thmEVEN_MULT, thmEVEN_ADD, defNUMERAL, thmBIT1, defEVEN]
         ]

thmMULT_AC :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmMULT_AC = cacheProof "thmMULT_AC" ctxtArithA .
    prove [str| (m * n = n * m) /\
                ((m * n) * p = m * (n * p)) /\
                (m * (n * p) = n * (m * p)) |] $
      tacMESON [thmMULT_ASSOC, thmMULT_SYM]

thmARITH_LT :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_LT = cacheProof "thmARITH_LT" ctxtArithA $
    prove [str| (!m n. NUMERAL m < NUMERAL n <=> m < n) /\
                ((_0 < _0) <=> F) /\
                (!n. (BIT0 n < _0) <=> F) /\
                (!n. (BIT1 n < _0) <=> F) /\
                (!n. (_0 < BIT0 n) <=> _0 < n) /\
                (!n. (_0 < BIT1 n) <=> T) /\
                (!m n. (BIT0 m < BIT0 n) <=> m < n) /\
                (!m n. (BIT0 m < BIT1 n) <=> m <= n) /\
                (!m n. (BIT1 m < BIT0 n) <=> m < n) /\
                (!m n. (BIT1 m < BIT1 n) <=> m < n) |] $
      tacREWRITE [defNUMERAL, ruleGSYM thmNOT_LE, thmARITH_LE] `_THEN`
      tacREWRITE [ruleDENUMERAL defLE]

thmARITH_GE :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_GE = cacheProof "thmARITH_GE" ctxtArithA $ 
    ruleREWRITE [ruleGSYM defGE, ruleGSYM defGT] thmARITH_LE

thmARITH_EQ :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmARITH_EQ = cacheProof "thmARITH_EQ" ctxtArithA $
    prove [str| (!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\
                ((_0 = _0) <=> T) /\
                 (!n. (BIT0 n = _0) <=> (n = _0)) /\
                 (!n. (BIT1 n = _0) <=> F) /\
                 (!n. (_0 = BIT0 n) <=> (_0 = n)) /\
                 (!n. (_0 = BIT1 n) <=> F) /\
                 (!m n. (BIT0 m = BIT0 n) <=> (m = n)) /\
                 (!m n. (BIT0 m = BIT1 n) <=> F) /\
                 (!m n. (BIT1 m = BIT0 n) <=> F) /\
                 (!m n. (BIT1 m = BIT1 n) <=> (m = n)) |] $
      tacREWRITE [defNUMERAL, ruleGSYM thmLE_ANTISYM, thmARITH_LE] `_THEN`
      tacREWRITE [thmLET_ANTISYM, thmLTE_ANTISYM, ruleDENUMERAL thmLE_0]

thmEXP_ADD :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmEXP_ADD = cacheProof "thmEXP_ADD" ctxtArithA .
    prove "!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)" $
      tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [defEXP, thmADD_CLAUSES, thmMULT_CLAUSES, thmMULT_AC]

thmDIVMOD_EXIST_0 :: (BasicConvs thry, ArithACtxt thry) => HOL cls thry HOLThm
thmDIVMOD_EXIST_0 = cacheProof "thmDIVMOD_EXIST_0" ctxtArithA .
    prove [str| !m n. ?q r. if n = 0 then q = 0 /\ r = m
                            else m = q * n + r /\ r < n |] $
      _REPEAT tacGEN `_THEN` tacASM_CASES "n = 0" `_THEN`
      tacASM_SIMP [thmDIVMOD_EXIST, thmRIGHT_EXISTS_AND, thmEXISTS_REFL]

specDIVISION_0' :: (BasicConvs thry, ArithACtxt thry) => HOL Theory thry HOLThm
specDIVISION_0' = newSpecification ["DIV", "MOD"] =<<
    ruleREWRITE [thmSKOLEM] thmDIVMOD_EXIST_0

defMinimal' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defMinimal' = newDefinition "minimal"
    [str| (minimal) (P:num->bool) = @n. P n /\ !m. m < n ==> ~(P m) |]
