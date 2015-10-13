module HaskHOL.Lib.Arith.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification,
                                 newSpecification, newDefinition)

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion

defPRE :: HOL cls thry HOLThm
defPRE = unsafeCacheProof "defPRE" $ getRecursiveDefinition "PRE"

defADD :: HOL cls thry HOLThm
defADD = unsafeCacheProof "defADD" $ getRecursiveDefinition "+"

defMULT :: HOL cls thry HOLThm
defMULT = unsafeCacheProof "defMULT" $ getRecursiveDefinition "*"

defLE :: HOL cls thry HOLThm
defLE = unsafeCacheProof "defLE" $ getRecursiveDefinition "<="

defLT :: HOL cls thry HOLThm
defLT = unsafeCacheProof "defLT" $ getRecursiveDefinition "<"

thmADD_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_0 = unsafeCacheProof "thmADD_0" .
    prove "!m. m + 0 = m" $ 
      tacINDUCT `_THEN` tacASM_REWRITE [defADD]

thmADD_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SUC = unsafeCacheProof "thmADD_SUC" .
    prove "!m n. m + (SUC n) = SUC (m + n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [defADD]

thmLE_SUC_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_SUC_LT = unsafeCacheProof "thmLE_SUC_LT" .
    prove "!m n. (SUC m <= n) <=> (m < n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [ defLE , defLT, thmNOT_SUC, thmSUC_INJ ]

thmLT_SUC_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_SUC_LE = unsafeCacheProof "thmLT_SUC_LE" .
    prove "!m n. (m < SUC n) <=> (m <= n)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacONCE_REWRITE [ defLT, defLE ] `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacREWRITE [defLT]

thmLE_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_0 = unsafeCacheProof "thmLE_0" .
    prove "!n. 0 <= n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defLE]

wfNUM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
wfNUM_PRIM = unsafeCacheProof "wfNUM_PRIM" .
    prove "!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n" $
      tacGEN `_THEN` 
      tacMP (ruleSPEC "\\n. !m. m < n ==> P m" inductionNUM) `_THEN`
      tacREWRITE [defLT, thmBETA] `_THEN` 
      tacMESON [defLT]

thmADD_CLAUSES :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_CLAUSES = unsafeCacheProof "thmADD_CLAUSES" .
    prove [str| (!n. 0 + n = n) /\
                (!m. m + 0 = m) /\
                (!m n. (SUC m) + n = SUC(m + n)) /\
                (!m n. m + (SUC n) = SUC(m + n)) |] $
      tacREWRITE [defADD, thmADD_0, thmADD_SUC]

thmLE_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_SUC = unsafeCacheProof "thmLE_SUC" .
    prove "!m n. (SUC m <= SUC n) <=> (m <= n)" $
      tacREWRITE [thmLE_SUC_LT, thmLT_SUC_LE]

thmLT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_SUC = unsafeCacheProof "thmLT_SUC" .
    prove "!m n. (SUC m < SUC n) <=> (m < n)" $
      tacREWRITE [thmLT_SUC_LE, thmLE_SUC_LT]

wopNUM :: NumsCtxt thry => HOL cls thry HOLThm
wopNUM = unsafeCacheProof "wopNUM" .
    prove [str| !P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m)) |] $
      tacGEN `_THEN` tacEQ `_THENL` [_ALL, tacMESON_NIL] `_THEN`
      tacCONV convCONTRAPOS `_THEN` tacREWRITE [thmNOT_EXISTS] `_THEN`
      tacDISCH `_THEN` tacMATCH_MP wfNUM_PRIM `_THEN` tacASM_MESON_NIL

thmADD_SYM :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_SYM = unsafeCacheProof "thmADD_SYM" .
    prove "!m n. m + n = n + m" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmEQ_ADD_LCANCEL :: NumsCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL = unsafeCacheProof "thmEQ_ADD_LCANCEL" .
    prove "!m n p. (m + n = m + p) <=> (n = p)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmBIT0 :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT0 = unsafeCacheProof "thmBIT0" .
    prove "!n. BIT0 n = n + n" $
      tacINDUCT `_THEN` tacASM_REWRITE [defBIT0, thmADD_CLAUSES]

thmMULT_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_0 = unsafeCacheProof "thmMULT_0" .
    prove "!m. m * 0 = 0" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defMULT, thmADD_CLAUSES]

thmADD_ASSOC :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_ASSOC = unsafeCacheProof "thmADD_ASSOC" .
    prove "!m n p. m + (n + p) = (m + n) + p" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]

thmADD_EQ_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmADD_EQ_0 = unsafeCacheProof "thmADD_EQ_0" .
    prove [str| !m n. (m + n = 0) <=> (m = 0) /\ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmNOT_SUC]

thmLT_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_0 = unsafeCacheProof "thmLT_0" .
    prove "!n. 0 < SUC n" $
      tacREWRITE [thmLT_SUC_LE, thmLE_0]

thmLT_ADD :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADD = unsafeCacheProof "thmLT_ADD" .
    prove "!m n. (m < m + n) <=> (0 < n)" $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmLT_SUC]

thmBIT1 :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT1 = unsafeCacheProof "thmBIT1" .
    prove "!n. BIT1 n = SUC(n + n)" $
      tacREWRITE [defBIT1, thmBIT0]

thmMULT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_SUC = unsafeCacheProof "thmMULT_SUC" .
    prove "!m n. m * (SUC n) = m + (m * n)" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defMULT, thmADD_CLAUSES, thmADD_ASSOC]

thmNOT_LE :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_LE = unsafeCacheProof "thmNOT_LE" .
    prove "!m n. ~(m <= n) <=> (n < m)" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ defLE, defLT, thmNOT_SUC
                 , ruleGSYM thmNOT_SUC, thmLE_0 ] `_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]


thmNOT_LT :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_LT = unsafeCacheProof "thmNOT_LT" .
    prove "!m n. ~(m < n) <=> n <= m" $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ defLE, defLT, thmNOT_SUC
                 , ruleGSYM thmNOT_SUC, thmLE_0 ] `_THEN`
      (\ g@(Goal _ asl) -> let a = head $ frees asl in
                             tacSPEC (a, a) g) `_THEN`
      tacINDUCT `_THEN` tacREWRITE [thmLT_0]

thmLE_EXISTS :: NumsCtxt thry => HOL cls thry HOLThm
thmLE_EXISTS = unsafeCacheProof "thmLE_EXISTS" .
    prove "!m n. (m <= n) <=> (?d. n = m + d)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defLE] `_THENL`
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

thmLT_ADDR :: NumsCtxt thry => HOL cls thry HOLThm
thmLT_ADDR = unsafeCacheProof "thmLT_ADDR" .
    prove "!m n. (n < m + n) <=> (0 < m)" $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLT_ADD

thmBIT1_THM :: NumsCtxt thry => HOL cls thry HOLThm
thmBIT1_THM = unsafeCacheProof "thmBIT1_THM" .
    prove "!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)" $
      tacREWRITE [defNUMERAL, thmBIT1]

thmMULT_CLAUSES :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_CLAUSES =  unsafeCacheProof "thmMULT_CLAUSES" .
    prove [str| (!n. 0 * n = 0) /\
                (!m. m * 0 = 0) /\
                (!n. 1 * n = n) /\
                (!m. m * 1 = m) /\
                (!m n. (SUC m) * n = (m * n) + n) /\
                (!m n. m * (SUC n) = m + (m * n)) |] $
      tacREWRITE [ thmBIT1_THM, defMULT, thmMULT_0
                 , thmMULT_SUC, thmADD_CLAUSES ]

thmMULT_SYM :: NumsCtxt thry => HOL cls thry HOLThm
thmMULT_SYM = unsafeCacheProof "thmMULT_SYM" .
    prove "!m n. m * n = n * m" $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmMULT_CLAUSES
                     , ruleEQT_INTRO =<< ruleSPEC_ALL thmADD_SYM ]

thmLEFT_ADD_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmLEFT_ADD_DISTRIB = unsafeCacheProof "thmLEFT_ADD_DISTRIB" .
    prove "!m n p. m * (n + p) = (m * n) + (m * p)" $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defADD, thmMULT_CLAUSES, thmADD_ASSOC]


thmRIGHT_ADD_DISTRIB :: NumsCtxt thry => HOL cls thry HOLThm
thmRIGHT_ADD_DISTRIB = unsafeCacheProof "thmRIGHT_ADD_DISTRIB" .
    prove "!m n p. (m + n) * p = (m * p) + (n * p)" $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_ADD_DISTRIB

thmDIVMOD_EXIST :: NumsCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST = unsafeCacheProof "thmDIVMOD_EXIST" .
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

thmDIVMOD_EXIST_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST_0 = unsafeCacheProof "thmDIVMOD_EXIST_0" .
    prove [str| !m n. ?q r. if n = 0 then q = 0 /\ r = m
                            else m = q * n + r /\ r < n |] $
      _REPEAT tacGEN `_THEN` tacASM_CASES "n = 0" `_THEN`
      tacASM_SIMP [thmDIVMOD_EXIST, thmRIGHT_EXISTS_AND, thmEXISTS_REFL]
