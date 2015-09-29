module HaskHOL.Lib.Arith.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification,
                                 newSpecification, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion


thmADD_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_0 =
    prove "!m. m + 0 = m" $ 
      tacINDUCT `_THEN` tacASM_REWRITE [getRecursiveDefinition "+"]

thmADD_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUC =
    prove "!m n. m + (SUC n) = SUC (m + n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [getRecursiveDefinition "+"]

thmLE_SUC_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_SUC_LT =
    prove "!m n. (SUC m <= n) <=> (m < n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [ getRecursiveDefinition "<=", getRecursiveDefinition "<"
                     , thmNOT_SUC, thmSUC_INJ ]

thmLT_SUC_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_SUC_LE =
    prove "!m n. (m < SUC n) <=> (m <= n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacONCE_REWRITE [ getRecursiveDefinition "<"
                      , getRecursiveDefinition "<=" ] `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacREWRITE [getRecursiveDefinition "<"]

thmLE_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_0 =
    prove "!n. 0 <= n" $
      tacINDUCT `_THEN` tacASM_REWRITE [getRecursiveDefinition "<="]

wfNUM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
wfNUM_PRIM =
    prove "!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n" $
      tacGEN `_THEN` 
      tacMP (ruleSPEC "\\n. !m. m < n ==> P m" inductionNUM) `_THEN`
      tacREWRITE [getRecursiveDefinition "<", thmBETA] `_THEN` 
      tacMESON [getRecursiveDefinition "<"]

thmSUB_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_0 = 
    prove [str| !m. (0 - m = 0) /\ (m - 0 = m) |] $
      tacREWRITE [getRecursiveDefinition "-"] `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "-", getRecursiveDefinition "PRE"]

thmSUB_PRESUC :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_PRESUC = 
    prove "!m n. PRE(SUC m - n) = m - n" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "-", getRecursiveDefinition "PRE"]

thmLE_REFL :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_REFL = 
    prove "!n. n <= n" $ tacINDUCT `_THEN` 
    tacREWRITE [getRecursiveDefinition "<="]

thmNOT_EVEN :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_EVEN =
    prove "!n. ~(EVEN n) <=> ODD n" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ getRecursiveDefinition "EVEN"
                     , getRecursiveDefinition "ODD" ]

thmNOT_ODD :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_ODD = 
    prove "!n. ~(ODD n) <=> EVEN n" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ getRecursiveDefinition "EVEN"
                     , getRecursiveDefinition "ODD" ]

thmADD_CLAUSES :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_CLAUSES =
    prove [str| (!n. 0 + n = n) /\
                (!m. m + 0 = m) /\
                (!m n. (SUC m) + n = SUC(m + n)) /\
                (!m n. m + (SUC n) = SUC(m + n)) |] $
      tacREWRITE [getRecursiveDefinition "+", thmADD_0, thmADD_SUC]
      
thmLE_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_SUC =
    prove "!m n. (SUC m <= SUC n) <=> (m <= n)" $
      tacREWRITE [thmLE_SUC_LT, thmLT_SUC_LE]

thmLT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_SUC =
    prove "!m n. (SUC m < SUC n) <=> (m < n)" $
      tacREWRITE [thmLT_SUC_LE, thmLE_SUC_LT]

wopNUM :: NumsCtxt thry => HOL cls thry HOLThm
wopNUM =
    prove [str| !P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m)) |] $
      tacGEN `_THEN` tacEQ `_THENL` [_ALL, tacMESON_NIL] `_THEN`
      tacCONV convCONTRAPOS `_THEN` tacREWRITE [thmNOT_EXISTS] `_THEN`
      tacDISCH `_THEN` tacMATCH_MP wfNUM_PRIM `_THEN` tacASM_MESON_NIL

thmSUB_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_SUC =
    prove "!m n. SUC m - SUC n = m - n" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ getRecursiveDefinition "-", getRecursiveDefinition "PRE"
                     , thmSUB_PRESUC ]

thmEVEN_OR_ODD :: NumsCtxt thry => HOL cls thry HOLThm
thmEVEN_OR_ODD = 
    prove [str| !n. EVEN n \/ ODD n |] $
      tacINDUCT `_THEN` 
      tacREWRITE [ getRecursiveDefinition "EVEN", getRecursiveDefinition "ODD"
                 , thmNOT_EVEN, thmNOT_ODD ] `_THEN`
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacASM_REWRITE_NIL

thmEVEN_AND_ODD :: NumsCtxt thry => HOL cls thry HOLThm
thmEVEN_AND_ODD =
    prove [str| !n. ~(EVEN n /\ ODD n) |] $
      tacREWRITE [ruleGSYM thmNOT_EVEN, ruleITAUT [str| ~(p /\ ~p) |]]

thmLET_CASES :: NumsCtxt thry => HOL cls thry HOLThm
thmLET_CASES =
    prove [str| !m n. m <= n \/ n < m |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC_LT, thmLT_SUC_LE, thmLE_0]

thmEQ_IMP_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_IMP_LE =
    prove "!m n. (m = n) ==> m <= n" $
      _REPEAT tacSTRIP `_THEN` tacASM_REWRITE [thmLE_REFL]

thmADD_SYM :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SYM = 
    prove "!m n. m + n = n + m" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmEQ_ADD_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL =
    prove "!m n p. (m + n = m + p) <=> (n = p)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmBIT0 :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT0 =
    prove "!n. BIT0 n = n + n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defBIT0, thmADD_CLAUSES]

thmMULT_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_0 =
    prove "!m. m * 0 = 0" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "*", thmADD_CLAUSES]

thmADD_ASSOC :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_ASSOC =
    prove "!m n p. m + (n + p) = (m + n) + p" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmADD_EQ_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_EQ_0 =
    prove [str| !m n. (m + n = 0) <=> (m = 0) /\ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmNOT_SUC]

thmLT_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_0 =
    prove "!n. 0 < SUC n" $
      tacREWRITE [thmLT_SUC_LE, thmLE_0]

thmLT_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADD = 
    prove "!m n. (m < m + n) <=> (0 < n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmLT_SUC]

thmADD_SUB :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUB =
    prove "!m n. (m + n) - n = m" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_SUC, thmSUB_0]

thmLT_REFL :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_REFL =
    prove "!n. ~(n < n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmLT_SUC] `_THEN` 
      tacREWRITE [getRecursiveDefinition "<"]

thmSUB_EQ_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_EQ_0 =
    prove "!m n. (m - n = 0) <=> m <= n" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmSUB_SUC, thmLE_SUC, thmSUB_0] `_THEN`
      tacREWRITE [getRecursiveDefinition "<=", thmLE_0]

thmLE_CASES :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_CASES = 
    prove [str| !m n. m <= n \/ n <= m |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_0, thmLE_SUC]

thmLE_ANTISYM :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ANTISYM = 
     prove [str| !m n. (m <= n /\ n <= m) <=> (m = n) |] $
       _REPEAT tacINDUCT `_THEN` 
       tacASM_REWRITE [thmLE_SUC, thmSUC_INJ] `_THEN`
       tacREWRITE [getRecursiveDefinition "<=", thmNOT_SUC, ruleGSYM thmNOT_SUC]

thmLET_ANTISYM :: NumsCtxt thry => HOL cls thry HOLThm
thmLET_ANTISYM =
    prove [str| !m n. ~(m <= n /\ n < m) |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ getRecursiveDefinition "<=", getRecursiveDefinition "<"
                 , thmNOT_SUC ]

thmEVEN_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmEVEN_ADD = 
    prove "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "EVEN", thmADD_CLAUSES] `_THEN`
      tacX_GEN "p:num" `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "n:num" thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "p:num" thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmLE_TRANS :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_TRANS =
    prove [str| !m n p. m <= n /\ n <= p ==> m <= p |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLE_0] `_THEN`
      tacREWRITE [getRecursiveDefinition "<=", thmNOT_SUC]
    
thmSUB_REFL :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_REFL =
    prove "!n. n - n = 0" $ 
      tacINDUCT `_THEN` tacASM_REWRITE [thmSUB_SUC, thmSUB_0]

thmLE_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ADD =
    prove "!m n. m <= m + n" $
      tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [getRecursiveDefinition "<=", thmADD_CLAUSES, thmLE_REFL]

thmLTE_CASES :: NumsCtxt thry => HOL cls thry HOLThm
thmLTE_CASES = 
    prove [str| !m n. m < n \/ n <= m |] $
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacMATCH_ACCEPT thmLET_CASES

thmSUB_ADD_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmSUB_ADD_LCANCEL =
    prove "!m n p. (m + n) - (m + p) = n - p" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_0, thmSUB_SUC]

thmBIT0_THM :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT0_THM = 
    prove "!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n" $
      tacREWRITE [defNUMERAL, thmBIT0]

thmBIT1 :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT1 = 
    prove "!n. BIT1 n = SUC(n + n)" $
      tacREWRITE [defBIT1, thmBIT0]

thmMULT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_SUC = 
    prove "!m n. m * (SUC n) = m + (m * n)" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "*", thmADD_CLAUSES, thmADD_ASSOC]

thmNOT_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_LE =
    prove "!m n. ~(m <= n) <=> (n < m)" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ getRecursiveDefinition "<=", getRecursiveDefinition "<"
                 , thmNOT_SUC, ruleGSYM thmNOT_SUC, thmLE_0 ] `_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]


thmNOT_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_LT =
    prove "!m n. ~(m < n) <=> n <= m" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ getRecursiveDefinition "<=", getRecursiveDefinition "<"
                 , thmNOT_SUC, ruleGSYM thmNOT_SUC, thmLE_0
                 ]`_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]

thmLE_EXISTS :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_EXISTS =
    prove "!m n. (m <= n) <=> (?d. n = m + d)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "<="] `_THENL`
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

thmLT_EXISTS :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_EXISTS = 
    prove "!m n. (m < n) <=> (?d. n = m + SUC d)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacREWRITE [ getRecursiveDefinition "<"
                 , thmADD_CLAUSES, ruleGSYM thmNOT_SUC ] `_THEN`
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

thmLT_ADDR :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADDR =
    prove "!m n. (n < m + n) <=> (0 < m)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLT_ADD

thmADD_SUB2 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUB2 = 
    prove "!m n. (m + n) - m = n" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUB

thmLTE_ANTISYM :: NumsCtxt thry => HOL cls thry HOLThm
thmLTE_ANTISYM =
    prove [str| !m n. ~(m < n /\ n <= m) |] $
      tacONCE_REWRITE [thmCONJ_SYM] `_THEN` tacREWRITE [thmLET_ANTISYM]

thmLE_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_LT =
    prove [str| !m n. (m <= n) <=> (m < n) \/ (m = n) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmLE_SUC, thmLT_SUC
                     , thmSUC_INJ, thmLE_0, thmLT_0 ] `_THEN`
      tacREWRITE [getRecursiveDefinition "<=", getRecursiveDefinition "<"]

thmARITH_ZERO :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_ZERO =
    prove [str| (NUMERAL 0 = 0) /\ (BIT0 _0 = _0) |] $
      tacREWRITE [defNUMERAL, thmBIT0, ruleDENUMERAL thmADD_CLAUSES]

thmADD_AC :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_AC = 
    prove [str| (m + n = n + m) /\
                ((m + n) + p = m + (n + p)) /\
                (m + (n + p) = n + (m + p)) |] $
      tacMESON [thmADD_ASSOC, thmADD_SYM]

thmODD_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmODD_ADD =
    prove "!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)" $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [ruleGSYM thmNOT_EVEN, thmEVEN_ADD] `_THEN`
      tacCONV (Conv ruleITAUT)

thmEQ_ADD_RCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_RCANCEL = 
    prove "!m n p. (m + p = n + p) <=> (m = n)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmEQ_ADD_LCANCEL

thmLTE_TRANS :: NumsCtxt thry => HOL cls thry HOLThm
thmLTE_TRANS =
    prove [str| !m n p. m < n /\ n <= p ==> m < p |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC, thmLT_0] `_THEN`
      tacREWRITE [ getRecursiveDefinition "<", getRecursiveDefinition "<="
                 , thmNOT_SUC ]

thmADD_SUBR2 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUBR2 =
    prove "!m n. m - (m + n) = 0" $
      tacREWRITE [thmSUB_EQ_0, thmLE_ADD]

thmEQ_ADD_LCANCEL_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL_0 =
    prove "!m n. (m + n = m) <=> (n = 0)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmLE_ADDR :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ADDR = 
    prove "!m n. n <= m + n" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLE_ADD

thmBIT1_THM :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT1_THM =
    prove "!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)" $
      tacREWRITE [defNUMERAL, thmBIT1]

thmLT_ADD_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADD_LCANCEL =
    prove "!m n p. (m + n) < (m + p) <=> n < p" $
      tacREWRITE [ thmLT_EXISTS, ruleGSYM thmADD_ASSOC
                 , thmEQ_ADD_LCANCEL, thmSUC_INJ ]

thmLE_ADD_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ADD_LCANCEL = 
    prove "!m n p. (m + n) <= (m + p) <=> n <= p" $
      tacREWRITE [thmLE_EXISTS, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmARITH_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_SUC = 
    prove [str| (!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
                (SUC _0 = BIT1 _0) /\
                (!n. SUC (BIT0 n) = BIT1 n) /\
                (!n. SUC (BIT1 n) = BIT0 (SUC n)) |] $
      tacREWRITE [defNUMERAL, thmBIT0, thmBIT1, ruleDENUMERAL thmADD_CLAUSES]

thmARITH_PRE :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_PRE = 
    do th <- ruleDENUMERAL (getRecursiveDefinition "PRE")
       prove [str| (!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
                   (PRE _0 = _0) /\
                   (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
                   (!n. PRE(BIT1 n) = BIT0 n) |] $
         tacREWRITE [defNUMERAL, thmBIT1, thmBIT0, return th ] `_THEN` 
         tacINDUCT `_THEN` tacREWRITE [ defNUMERAL, return th
                                      , ruleDENUMERAL thmADD_CLAUSES
                                      , ruleDENUMERAL thmNOT_SUC, thmARITH_ZERO 
                                      ]

thmARITH_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_ADD = 
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

thmARITH_EVEN :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_EVEN =
    prove [str| (!n. EVEN(NUMERAL n) <=> EVEN n) /\
                (EVEN _0 <=> T) /\
                (!n. EVEN(BIT0 n) <=> T) /\
                (!n. EVEN(BIT1 n) <=> F) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                 , ruleDENUMERAL (getRecursiveDefinition "EVEN")
                 , thmEVEN_ADD ]

thmARITH_ODD :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_ODD = 
    prove [str| (!n. ODD(NUMERAL n) <=> ODD n) /\
                (ODD _0 <=> F) /\
                (!n. ODD(BIT0 n) <=> F) /\
                (!n. ODD(BIT1 n) <=> T) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                 , ruleDENUMERAL (getRecursiveDefinition "ODD"), thmODD_ADD ]

thmLE_ADD2 :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ADD2 =
    prove [str| !m n p q. m <= p /\ n <= q ==> m + n <= p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN 
        (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
         (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a + b" `_THEN` tacASM_REWRITE [thmADD_AC]

thmADD_SUBR :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUBR = 
    prove "!m n. n - (m + n) = 0" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUBR2

thmLT_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_LE =
    prove [str| !m n. (m < n) <=> (m <= n) /\ ~(m = n) |] $
      tacREWRITE [thmLE_LT] `_THEN` _REPEAT tacGEN `_THEN` tacEQ `_THENL`
      [ tacDISCH `_THEN` tacASM_REWRITE_NIL `_THEN` 
        _DISCH_THEN tacSUBST_ALL `_THEN` _POP_ASSUM tacMP `_THEN`
        tacREWRITE [thmLT_REFL]
      , _DISCH_THEN (_CONJUNCTS_THEN2 tacSTRIP_ASSUME tacMP) `_THEN`
        tacASM_REWRITE_NIL
      ]

thmLET_ADD2 :: NumsCtxt thry => HOL cls thry HOLThm
thmLET_ADD2 = 
    prove [str| !m n p q. m <= p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS, thmLT_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
                     (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a + b" `_THEN` 
      tacASM_REWRITE [thmSUC_INJ, thmADD_CLAUSES, thmADD_AC]

thmADD1 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD1 =
    prove "!m. SUC m = m + 1" $
      tacREWRITE [thmBIT1_THM, thmADD_CLAUSES]

thmMULT_CLAUSES :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_CLAUSES = 
    prove [str| (!n. 0 * n = 0) /\
                (!m. m * 0 = 0) /\
                (!n. 1 * n = n) /\
                (!m. m * 1 = m) /\
                (!m n. (SUC m) * n = (m * n) + n) /\
                (!m n. m * (SUC n) = m + (m * n)) |] $
      tacREWRITE [ thmBIT1_THM, getRecursiveDefinition "*", thmMULT_0
                 , thmMULT_SUC, thmADD_CLAUSES ]

thmLT_IMP_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_IMP_LE = 
    prove "!m n. m < n ==> m <= n" $
      tacREWRITE [thmLT_LE] `_THEN` _REPEAT tacSTRIP `_THEN` 
      tacASM_REWRITE_NIL

thmLE_ADD_RCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_ADD_RCANCEL = 
    prove "!m n p. (m + p) <= (n + p) <=> (m <= n)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmLE_ADD_LCANCEL

thmLTE_ADD2 :: NumsCtxt thry => HOL cls thry HOLThm
thmLTE_ADD2 = 
    prove [str| !m n p q. m < p /\ n <= q ==> m + n < p + q |] $
      tacONCE_REWRITE [thmADD_SYM, thmCONJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLET_ADD2

thmMULT_SYM :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_SYM = 
    prove "!m n. m * n = n * m" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmMULT_CLAUSES
                     , ruleEQT_INTRO =<< ruleSPEC_ALL thmADD_SYM ]

thmLEFT_ADD_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmLEFT_ADD_DISTRIB = 
    prove "!m n p. m * (n + p) = (m * n) + (m * p)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [getRecursiveDefinition "+", thmMULT_CLAUSES, thmADD_ASSOC]

thmLE_MULT_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_MULT_LCANCEL = 
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [str| !m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                        , thmLE_REFL, thmLE_0, thmNOT_SUC ] `_THEN`
         tacREWRITE [thmLE_SUC] `_THEN`
         tacREWRITE [ getRecursiveDefinition "<="
                    , thmLE_ADD_LCANCEL, ruleGSYM thmADD_ASSOC ] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmLT_MULT_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_MULT_LCANCEL = 
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [str| !m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                        , thmLT_REFL, thmLT_0, thmNOT_SUC] `_THEN`
         tacREWRITE [thmLT_SUC] `_THEN`
         tacREWRITE [ getRecursiveDefinition "<"
                    , thmLT_ADD_LCANCEL, ruleGSYM thmADD_ASSOC ] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmMULT_EQ_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_EQ_0 =
    prove [str| !m n. (m * n = 0) <=> (m = 0) \/ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES, thmNOT_SUC]

thmEQ_MULT_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_MULT_LCANCEL = 
    prove [str| !m n p. (m * n = m * p) <=> (m = 0) \/ (n = p) |] $
      tacINDUCT `_THEN` tacREWRITE [thmMULT_CLAUSES, thmNOT_SUC] `_THEN`
      _REPEAT tacINDUCT `_THEN`
      tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                     , ruleGSYM thmNOT_SUC, thmNOT_SUC ] `_THEN`
      tacASM_REWRITE [thmSUC_INJ, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmEVEN_MULT :: NumsCtxt thry => HOL cls thry HOLThm
thmEVEN_MULT = 
    prove [str| !m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n) |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmMULT_CLAUSES, thmEVEN_ADD
                     , getRecursiveDefinition "EVEN" ] `_THEN`
      tacX_GEN "p:num" `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "n:num" thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC "p:num" thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmEXP_EQ_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmEXP_EQ_0 = 
    prove [str| !m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmBIT1_THM, thmNOT_SUC, getRecursiveDefinition "EXP"
                     , thmMULT_CLAUSES, thmADD_CLAUSES, thmADD_EQ_0 ]

thmLT_ADD2 :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADD2 = 
    prove [str| !m n p q. m < p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacSTRIP `_THEN` tacMATCH_MP thmLTE_ADD2 `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacMATCH_MP thmLT_IMP_LE `_THEN`
      tacASM_REWRITE_NIL

thmRIGHT_ADD_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmRIGHT_ADD_DISTRIB =
    prove "!m n p. (m + n) * p = (m * p) + (n * p)" $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_ADD_DISTRIB

thmLEFT_SUB_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmLEFT_SUB_DISTRIB =
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

thmEVEN_DOUBLE :: NumsCtxt thry => HOL cls thry HOLThm
thmEVEN_DOUBLE =
    prove "!n. EVEN(2 * n)" $
      tacGEN `_THEN` tacREWRITE [thmEVEN_MULT] `_THEN` tacDISJ1 `_THEN`
      tacPURE_REWRITE [thmBIT0_THM, thmBIT1_THM] `_THEN` 
      tacREWRITE [getRecursiveDefinition "EVEN", thmEVEN_ADD]

thmLE_MULT_RCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_MULT_RCANCEL =
    prove [str| !m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0) |] $
      tacONCE_REWRITE [thmMULT_SYM, thmDISJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLE_MULT_LCANCEL

thmDIVMOD_EXIST :: NumsCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST = 
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
      tacASM_REWRITE [ruleGSYM thmNOT_LE, getRecursiveDefinition "<="]

thmMULT_2 :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_2 = 
    prove "!n. 2 * n = n + n" $
      tacGEN `_THEN` 
      tacREWRITE [thmBIT0_THM, thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmARITH_MULT :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_MULT = 
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

thmMULT_ASSOC :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_ASSOC = 
    prove "!m n p. m * (n * p) = (m * n) * p" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmLE_MULT2 :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_MULT2 = 
    prove [str| !m n p q. m <= n /\ p <= q ==> m * p <= n * q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "a:num") 
                     (tacX_CHOOSE "b:num")) `_THEN`
      tacEXISTS "a * p + m * b + a * b" `_THEN`
      tacASM_REWRITE [thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB, thmADD_ASSOC]

thmRIGHT_SUB_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmRIGHT_SUB_DISTRIB =
    prove "!m n p. (m - n) * p = m * p - n * p" $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_SUB_DISTRIB

thmARITH_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_LE = 
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
         tacREWRITE [ ruleDENUMERAL (getRecursiveDefinition "<=")
                    , ruleGSYM thmMULT_2 ] `_THEN`
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
           tacREWRITE [ thmEVEN_MULT, thmEVEN_ADD, defNUMERAL, thmBIT1
                      , getRecursiveDefinition "EVEN" ]
         ]

thmMULT_AC :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_AC =
    prove [str| (m * n = n * m) /\
                ((m * n) * p = m * (n * p)) /\
                (m * (n * p) = n * (m * p)) |] $
      tacMESON [thmMULT_ASSOC, thmMULT_SYM]

thmARITH_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_LT =
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
      tacREWRITE [ruleDENUMERAL (getRecursiveDefinition "<=")]

thmARITH_GE :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_GE = 
    ruleREWRITE [ ruleGSYM (getDefinition ">=")
                , ruleGSYM (getDefinition ">")] thmARITH_LE

thmARITH_EQ :: NumsCtxt thry => HOL cls thry HOLThm
thmARITH_EQ = 
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

thmEXP_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmEXP_ADD =
    prove "!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)" $
      tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [ getRecursiveDefinition "EXP"
                     , thmADD_CLAUSES, thmMULT_CLAUSES, thmMULT_AC ]

thmDIVMOD_EXIST_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST_0 = 
    prove [str| !m n. ?q r. if n = 0 then q = 0 /\ r = m
                            else m = q * n + r /\ r < n |] $
      _REPEAT tacGEN `_THEN` tacASM_CASES "n = 0" `_THEN`
      tacASM_SIMP [thmDIVMOD_EXIST, thmRIGHT_EXISTS_AND, thmEXISTS_REFL]
