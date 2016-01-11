{-|
  Module:    HaskHOL.Lib.Arith
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Arith 
    ( ArithCtxt
    , ctxtArith
    , arith
    , defPRE
    , defADD
    , defMULT
    , defEXP
    , defLE
    , defLT
    , defGE
    , defGT
    , defMAX
    , defMIN
    , defEVEN
    , defODD
    , defSUB
    , defFACT
    , thmADD_0
    , thmADD_SUC
    , thmLE_SUC_LT
    , thmLT_SUC_LE
    , thmLE_0
    , wfNUM_PRIM
    , thmSUB_0
    , thmSUB_PRESUC
    , thmLE_REFL
    , thmNOT_EVEN
    , thmNOT_ODD
    , thmADD_CLAUSES
    , thmLE_SUC
    , thmLT_SUC
    , wopNUM
    , thmSUB_SUC
    , thmEVEN_OR_ODD
    , thmEVEN_AND_ODD
    , thmLET_CASES
    , thmEQ_IMP_LE
    , thmADD_SYM
    , thmEQ_ADD_LCANCEL
    , thmBIT0
    , thmMULT_0
    , thmADD_ASSOC
    , thmADD_EQ_0
    , thmLT_0
    , thmLT_ADD
    , thmADD_SUB
    , thmLT_REFL
    , thmSUB_EQ_0
    , thmLE_CASES
    , thmLE_ANTISYM
    , thmLET_ANTISYM
    , thmEVEN_ADD
    , thmLE_TRANS
    , thmSUB_REFL
    , thmLE_ADD
    , thmLTE_CASES
    , thmSUB_ADD_LCANCEL
    , thmBIT0_THM
    , thmBIT1
    , thmMULT_SUC
    , thmNOT_LE
    , thmNOT_LT
    , thmLE_EXISTS
    , thmLT_EXISTS
    , thmLT_ADDR
    , thmADD_SUB2
    , thmLTE_ANTISYM
    , thmLE_LT
    , thmARITH_ZERO
    , thmADD_AC
    , thmODD_ADD
    , thmEQ_ADD_RCANCEL
    , thmLTE_TRANS
    , thmADD_SUBR2
    , thmEQ_ADD_LCANCEL_0
    , thmLE_ADDR
    , thmBIT1_THM
    , thmLT_ADD_LCANCEL
    , thmLE_ADD_LCANCEL
    , thmARITH_SUC
    , thmARITH_PRE
    , thmARITH_ADD
    , thmARITH_EVEN
    , thmARITH_ODD
    , thmLE_ADD2
    , thmADD_SUBR
    , thmLT_LE
    , thmLET_ADD2
    , thmADD1
    , thmMULT_CLAUSES
    , thmLT_IMP_LE
    , thmLE_ADD_RCANCEL
    , thmLTE_ADD2
    , thmMULT_SYM
    , thmLEFT_ADD_DISTRIB
    , thmLE_MULT_LCANCEL
    , thmLT_MULT_LCANCEL
    , thmMULT_EQ_0
    , thmEQ_MULT_LCANCEL
    , thmEVEN_MULT
    , thmEXP_EQ_0
    , thmLT_ADD2
    , thmRIGHT_ADD_DISTRIB
    , thmLEFT_SUB_DISTRIB
    , thmEVEN_DOUBLE
    , thmLE_MULT_RCANCEL
    , thmDIVMOD_EXIST
    , thmMULT_2
    , thmDIVMOD_EXIST_0
    , specDIVISION_0
    , defMinimal
    , thmARITH_MULT
    , thmMULT_ASSOC
    , thmLE_MULT2
    , thmRIGHT_SUB_DISTRIB
    , thmARITH_LE
    , thmEXP_ADD
    , thmMULT_AC
    , thmARITH_LT
    , thmARITH_GE
    , thmARITH_EQ
    , thmONE
    , thmTWO
    , thmARITH_EXP 
    , thmARITH_GT
    , thmARITH_SUB
    , thmARITH_0
    , thmBITS_INJ
    , thmSUB_ELIM
    , thmEXP_2
    , convNUM_CANCEL
    , ruleLE_IMP
    , thmDIVISION
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion

import qualified HaskHOL.Lib.Arith.Base as Base
import HaskHOL.Lib.Arith.Context
import HaskHOL.Lib.Arith.PQ

-- definitions
defPRE :: ArithCtxt thry => HOL cls thry HOLThm
defPRE = Base.defPRE

defADD :: ArithCtxt thry => HOL cls thry HOLThm
defADD = Base.defADD

defMULT :: ArithCtxt thry => HOL cls thry HOLThm
defMULT = Base.defMULT

defEXP :: ArithCtxt thry => HOL cls thry HOLThm
defEXP = cacheProof "defEXP" ctxtArith $ getRecursiveDefinition "EXP"

defLE :: ArithCtxt thry => HOL cls thry HOLThm
defLE = Base.defLE

defLT :: ArithCtxt thry => HOL cls thry HOLThm
defLT = Base.defLT

defGE :: ArithCtxt thry => HOL cls thry HOLThm
defGE = cacheProof "defGE" ctxtArith $ getDefinition ">="

defGT :: ArithCtxt thry => HOL cls thry HOLThm
defGT = cacheProof "defGT" ctxtArith $ getDefinition ">"

defMAX :: ArithCtxt thry => HOL cls thry HOLThm
defMAX = cacheProof "defMAX" ctxtArith $ getDefinition "MAX"

defMIN :: ArithCtxt thry => HOL cls thry HOLThm
defMIN = cacheProof "defMIN" ctxtArith $ getDefinition "MIN"

defEVEN :: ArithCtxt thry => HOL cls thry HOLThm
defEVEN = cacheProof "defEVEN" ctxtArith $ getRecursiveDefinition "EVEN"

defODD :: ArithCtxt thry => HOL cls thry HOLThm
defODD = cacheProof "defODD" ctxtArith $ getRecursiveDefinition "ODD"

defSUB :: ArithCtxt thry => HOL cls thry HOLThm
defSUB = cacheProof "defSUB" ctxtArith $ getRecursiveDefinition "-"

defFACT :: ArithCtxt thry => HOL cls thry HOLThm
defFACT = cacheProof "defFACT" ctxtArith $ getRecursiveDefinition "FACT"
       
specDIVISION_0 :: ArithCtxt thry => HOL cls thry HOLThm
specDIVISION_0 = cacheProof "specDIVISION_0" ctxtArith $ 
    getSpecification ["DIV", "MOD"]

defMinimal :: ArithCtxt thry => HOL cls thry HOLThm
defMinimal = cacheProof "defMinimal" ctxtArith $ getDefinition "minimal"


-- theorems
thmADD_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_0 = Base.thmADD_0

thmADD_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUC = Base.thmADD_SUC

thmLE_SUC_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_SUC_LT = Base.thmLE_SUC_LT

thmLT_SUC_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_SUC_LE = Base.thmLT_SUC_LE

thmLE_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_0 = Base.thmLE_0

wfNUM_PRIM :: ArithCtxt thry => HOL cls thry HOLThm
wfNUM_PRIM = Base.wfNUM_PRIM

thmSUB_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_0 = cacheProof "thmSUB_0" ctxtArith .
    prove [txt| !m. (0 - m = 0) /\ (m - 0 = m) |] $
      tacREWRITE [defSUB] `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defSUB, defPRE]

thmSUB_PRESUC :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_PRESUC = cacheProof "thmSUB_PRESUC" ctxtArith .
    prove [txt| !m n. PRE(SUC m - n) = m - n |] $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [defSUB, defPRE]

thmLE_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_REFL = cacheProof "thmLE_REFL" ctxtArith .
    prove [txt| !n. n <= n |] $ 
      tacINDUCT `_THEN` 
      tacREWRITE [defLE]

thmNOT_EVEN :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_EVEN = cacheProof "thmNOT_EVEN" ctxtArith .
    prove [txt| !n. ~(EVEN n) <=> ODD n |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defEVEN, defODD]

thmNOT_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_ODD = cacheProof "thmNOT_ODD" ctxtArith .
    prove [txt| !n. ~(ODD n) <=> EVEN n |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defEVEN, defODD]

thmADD_CLAUSES :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_CLAUSES = Base.thmADD_CLAUSES

thmLE_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_SUC = Base.thmLE_SUC

thmLT_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_SUC = Base.thmLT_SUC

wopNUM :: ArithCtxt thry => HOL cls thry HOLThm
wopNUM = Base.wopNUM

thmSUB_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_SUC = cacheProof "thmSUB_SUC" ctxtArith .
    prove [txt| !m n. SUC m - SUC n = m - n |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ defSUB, defPRE, thmSUB_PRESUC ]

thmEVEN_OR_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_OR_ODD = cacheProof "thmEVEN_OR_ODD" ctxtArith .
    prove [txt| !n. EVEN n \/ ODD n |] $
      tacINDUCT `_THEN` 
      tacREWRITE [ defEVEN, defODD, thmNOT_EVEN, thmNOT_ODD ] `_THEN`
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacASM_REWRITE_NIL

thmEVEN_AND_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_AND_ODD = cacheProof "thmEVEN_AND_ODD" ctxtArith .
    prove [txt| !n. ~(EVEN n /\ ODD n) |] $
      tacREWRITE [ruleGSYM thmNOT_EVEN, ruleITAUT [txt| ~(p /\ ~p) |]]

thmLET_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_CASES = cacheProof "thmLET_CASES" ctxtArith .
    prove [txt| !m n. m <= n \/ n < m |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC_LT, thmLT_SUC_LE, thmLE_0]

thmEQ_IMP_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_IMP_LE = cacheProof "thmEQ_IMP_LE" ctxtArith .
    prove [txt| !m n. (m = n) ==> m <= n |] $
      _REPEAT tacSTRIP `_THEN` tacASM_REWRITE [thmLE_REFL]

thmADD_SYM :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SYM = Base.thmADD_SYM

thmEQ_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL = Base.thmEQ_ADD_LCANCEL

thmBIT0 :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT0 = Base.thmBIT0

thmMULT_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_0 = Base.thmMULT_0

thmADD_ASSOC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_ASSOC = Base.thmADD_ASSOC

thmADD_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_EQ_0 = Base.thmADD_EQ_0

thmLT_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_0 = Base.thmLT_0

thmLT_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD = Base.thmLT_ADD

thmADD_SUB :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUB = cacheProof "thmADD_SUB" ctxtArith .
    prove [txt| !m n. (m + n) - n = m |] $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_SUC, thmSUB_0]

thmLT_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_REFL = cacheProof "thmLT_REFL" ctxtArith .
    prove [txt| !n. ~(n < n) |] $
      tacINDUCT `_THEN` tacASM_REWRITE [thmLT_SUC] `_THEN` 
      tacREWRITE [defLT]

thmSUB_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_EQ_0 = cacheProof "thmSUB_EQ_0" ctxtArith .
    prove [txt| !m n. (m - n = 0) <=> m <= n |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmSUB_SUC, thmLE_SUC, thmSUB_0] `_THEN`
      tacREWRITE [defLE, thmLE_0]

thmLE_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_CASES = cacheProof "thmLE_CASES" ctxtArith .
    prove [txt| !m n. m <= n \/ n <= m |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_0, thmLE_SUC]

thmLE_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ANTISYM = cacheProof "thmLE_ANTISYM" ctxtArith .
    prove [txt| !m n. (m <= n /\ n <= m) <=> (m = n) |] $
       _REPEAT tacINDUCT `_THEN` 
       tacASM_REWRITE [thmLE_SUC, thmSUC_INJ] `_THEN`
       tacREWRITE [defLE, thmNOT_SUC, ruleGSYM thmNOT_SUC]

thmLET_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_ANTISYM = cacheProof "thmLET_ANTISYM" ctxtArith .
    prove [txt| !m n. ~(m <= n /\ n < m) |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLT_SUC] `_THEN`
      tacREWRITE [ defLE, defLT, thmNOT_SUC ]

thmEVEN_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_ADD = cacheProof "thmEVEN_ADD" ctxtArith .
    prove [txt| !m n. EVEN(m + n) <=> (EVEN m <=> EVEN n) |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [defEVEN, thmADD_CLAUSES] `_THEN`
      tacX_GEN [txt| p:num |] `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC [txt| n:num |] thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC [txt| p:num |] thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmLE_TRANS :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_TRANS = cacheProof "thmLE_TRANS" ctxtArith .
    prove [txt| !m n p. m <= n /\ n <= p ==> m <= p |] $
      _REPEAT tacINDUCT `_THEN` tacASM_REWRITE [thmLE_SUC, thmLE_0] `_THEN`
      tacREWRITE [defLE, thmNOT_SUC]

thmSUB_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_REFL = cacheProof "thmSUB_REFL" ctxtArith .
    prove [txt| !n. n - n = 0 |] $ 
      tacINDUCT `_THEN` tacASM_REWRITE [thmSUB_SUC, thmSUB_0]

thmLE_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD = cacheProof "thmLE_ADD" ctxtArith .
    prove [txt| !m n. m <= m + n |] $
      tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [defLE, thmADD_CLAUSES, thmLE_REFL]

thmLTE_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_CASES = cacheProof "thmLTE_CASES" ctxtArith .
    prove [txt| !m n. m < n \/ n <= m |] $
      tacONCE_REWRITE [thmDISJ_SYM] `_THEN` tacMATCH_ACCEPT thmLET_CASES

thmSUB_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_ADD_LCANCEL = cacheProof "thmSUB_ADD_LCANCEL" ctxtArith .
    prove [txt| !m n p. (m + n) - (m + p) = n - p |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [thmADD_CLAUSES, thmSUB_0, thmSUB_SUC]

thmBIT0_THM :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT0_THM = cacheProof "thmBIT0_THM" ctxtArith .
    prove [txt| !n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n |] $
      tacREWRITE [defNUMERAL, thmBIT0]

thmBIT1 :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT1 = Base.thmBIT1

thmMULT_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_SUC = Base.thmMULT_SUC

thmNOT_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_LE = Base.thmNOT_LE

thmNOT_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_LT = Base.thmNOT_LT

thmLE_EXISTS :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_EXISTS = Base.thmLE_EXISTS

thmLT_EXISTS :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_EXISTS = cacheProof "thmLT_EXISTS" ctxtArith .
    prove [txt| !m n. (m < n) <=> (?d. n = m + SUC d) |] $
      tacGEN `_THEN` tacINDUCT `_THEN` 
      tacREWRITE [ defLT, thmADD_CLAUSES, ruleGSYM thmNOT_SUC ] `_THEN`
      tacASM_REWRITE [thmSUC_INJ] `_THEN` tacEQ `_THENL`
      [ _DISCH_THEN (_DISJ_CASES_THEN2 tacSUBST1 tacMP) `_THENL`
        [ tacEXISTS [txt| 0 |] `_THEN` tacREWRITE [thmADD_CLAUSES]
        , _DISCH_THEN (_X_CHOOSE_THEN [txt| d:num |] tacSUBST1) `_THEN`
          tacEXISTS [txt| SUC d |] `_THEN` tacREWRITE [thmADD_CLAUSES]
        ]
      , tacONCE_REWRITE [thmLEFT_IMP_EXISTS] `_THEN`
        tacINDUCT `_THEN` tacREWRITE [thmADD_CLAUSES, thmSUC_INJ] `_THEN`
        _DISCH_THEN tacSUBST1 `_THEN` tacREWRITE_NIL `_THEN` 
        tacDISJ2 `_THEN` tacREWRITE [ thmSUC_INJ, thmEQ_ADD_LCANCEL
                                    , ruleGSYM thmEXISTS_REFL ]
      ]

thmLT_ADDR :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADDR = Base.thmLT_ADDR

thmADD_SUB2 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUB2 = cacheProof "thmADD_SUB2" ctxtArith .
    prove [txt| !m n. (m + n) - m = n |] $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUB

thmLTE_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_ANTISYM = cacheProof "thmLTE_ANTISYM" ctxtArith .
    prove [txt| !m n. ~(m < n /\ n <= m) |] $
      tacONCE_REWRITE [thmCONJ_SYM] `_THEN` tacREWRITE [thmLET_ANTISYM]

thmLE_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_LT = cacheProof "thmLE_LT" ctxtArith .
    prove [txt| !m n. (m <= n) <=> (m < n) \/ (m = n) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmLE_SUC, thmLT_SUC
                     , thmSUC_INJ, thmLE_0, thmLT_0 ] `_THEN`
      tacREWRITE [defLE, defLT]

thmARITH_ZERO :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ZERO = cacheProof "thmARITH_ZERO" ctxtArith .
    prove [txt| (NUMERAL 0 = 0) /\ (BIT0 _0 = _0) |] $
      tacREWRITE [defNUMERAL, thmBIT0, ruleDENUMERAL thmADD_CLAUSES]

thmADD_AC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_AC = cacheProof "thmADD_AC" ctxtArith .
    prove [txt| (m + n = n + m) /\
                ((m + n) + p = m + (n + p)) /\
                (m + (n + p) = n + (m + p)) |] $
      tacMESON [thmADD_ASSOC, thmADD_SYM]

thmODD_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmODD_ADD = cacheProof "thmODD_ADD" ctxtArith .
    prove [txt| !m n. ODD(m + n) <=> ~(ODD m <=> ODD n) |] $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [ruleGSYM thmNOT_EVEN, thmEVEN_ADD] `_THEN`
      tacCONV (Conv ruleITAUT)

thmEQ_ADD_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_RCANCEL = cacheProof "thmEQ_ADD_RCANCEL" ctxtArith .
    prove [txt| !m n p. (m + p = n + p) <=> (m = n) |] $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmEQ_ADD_LCANCEL

thmLTE_TRANS :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_TRANS = cacheProof "thmLTE_TRANS" ctxtArith .
    prove [txt| !m n p. m < n /\ n <= p ==> m < p |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [thmLE_SUC, thmLT_SUC, thmLT_0] `_THEN`
      tacREWRITE [ defLT, defLE, thmNOT_SUC ]

thmADD_SUBR2 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUBR2 = cacheProof "thmADD_SUBR2" ctxtArith .
    prove [txt| !m n. m - (m + n) = 0 |] $
      tacREWRITE [thmSUB_EQ_0, thmLE_ADD]

thmEQ_ADD_LCANCEL_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL_0 = cacheProof "thmEQ_ADD_LCANCEL_0" ctxtArith .
    prove [txt| !m n. (m + n = m) <=> (n = 0) |] $
      tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES, thmSUC_INJ]

thmLE_ADDR :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADDR = cacheProof "thmLE_ADDR" ctxtArith .
    prove [txt| !m n. n <= m + n |] $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmLE_ADD

thmBIT1_THM :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT1_THM = Base.thmBIT1_THM

thmLT_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD_LCANCEL = cacheProof "thmLT_ADD_LCANCEL" ctxtArith .
    prove [txt| !m n p. (m + n) < (m + p) <=> n < p |] $
      tacREWRITE [ thmLT_EXISTS, ruleGSYM thmADD_ASSOC
                 , thmEQ_ADD_LCANCEL, thmSUC_INJ ]

thmLE_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD_LCANCEL = cacheProof "thmLE_ADD_LCANCEL" ctxtArith .
    prove [txt| !m n p. (m + n) <= (m + p) <=> n <= p |] $
      tacREWRITE [thmLE_EXISTS, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmARITH_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_SUC = cacheProof "thmARITH_SUC" ctxtArith .
    prove [txt| (!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\
                (SUC _0 = BIT1 _0) /\
                (!n. SUC (BIT0 n) = BIT1 n) /\
                (!n. SUC (BIT1 n) = BIT0 (SUC n)) |] $
      tacREWRITE [defNUMERAL, thmBIT0, thmBIT1, ruleDENUMERAL thmADD_CLAUSES]

thmARITH_PRE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_PRE = cacheProof "thmARITH_PRE" ctxtArith $
    do th <- ruleDENUMERAL defPRE
       prove [txt| (!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\
                   (PRE _0 = _0) /\
                   (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\
                   (!n. PRE(BIT1 n) = BIT0 n) |] $
         tacREWRITE [defNUMERAL, thmBIT1, thmBIT0, return th ] `_THEN` 
         tacINDUCT `_THEN` tacREWRITE [ defNUMERAL, return th
                                      , ruleDENUMERAL thmADD_CLAUSES
                                      , ruleDENUMERAL thmNOT_SUC, thmARITH_ZERO 
                                      ]

thmARITH_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ADD = cacheProof "thmARITH_ADD" ctxtArith .
    prove [txt| (!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\
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

thmARITH_EVEN :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EVEN = cacheProof "thmARITH_EVEN" ctxtArith .
    prove [txt| (!n. EVEN(NUMERAL n) <=> EVEN n) /\
                (EVEN _0 <=> T) /\
                (!n. EVEN(BIT0 n) <=> T) /\
                (!n. EVEN(BIT1 n) <=> F) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                 , ruleDENUMERAL defEVEN
                 , thmEVEN_ADD ]

thmARITH_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ODD = cacheProof "thmARITH_ODD" ctxtArith .
    prove [txt| (!n. ODD(NUMERAL n) <=> ODD n) /\
                (ODD _0 <=> F) /\
                (!n. ODD(BIT0 n) <=> F) /\
                (!n. ODD(BIT1 n) <=> T) |] $
      tacREWRITE [ defNUMERAL, thmBIT1, thmBIT0
                 , ruleDENUMERAL defODD, thmODD_ADD ]

thmLE_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD2 = cacheProof "thmLE_ADD2" ctxtArith .
    prove [txt| !m n p q. m <= p /\ n <= q ==> m + n <= p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN 
        (_CONJUNCTS_THEN2 (tacX_CHOOSE [txt| a:num |]) 
         (tacX_CHOOSE [txt| b:num |])) `_THEN`
      tacEXISTS [txt| a + b |] `_THEN` tacASM_REWRITE [thmADD_AC]

thmADD_SUBR :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUBR = cacheProof "thmADD_SUBR" ctxtArith .
    prove [txt| !m n. n - (m + n) = 0 |] $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` tacMATCH_ACCEPT thmADD_SUBR2

thmLT_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_LE = cacheProof "thmLT_LE" ctxtArith .
    prove [txt| !m n. (m < n) <=> (m <= n) /\ ~(m = n) |] $
      tacREWRITE [thmLE_LT] `_THEN` _REPEAT tacGEN `_THEN` tacEQ `_THENL`
      [ tacDISCH `_THEN` tacASM_REWRITE_NIL `_THEN` 
        _DISCH_THEN tacSUBST_ALL `_THEN` _POP_ASSUM tacMP `_THEN`
        tacREWRITE [thmLT_REFL]
      , _DISCH_THEN (_CONJUNCTS_THEN2 tacSTRIP_ASSUME tacMP) `_THEN`
        tacASM_REWRITE_NIL
      ]

thmLET_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_ADD2 = cacheProof "thmLET_ADD2" ctxtArith .
    prove [txt| !m n p q. m <= p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS, thmLT_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE [txt| a:num |]) 
                     (tacX_CHOOSE [txt| b:num |])) `_THEN`
      tacEXISTS [txt| a + b |] `_THEN` 
      tacASM_REWRITE [thmSUC_INJ, thmADD_CLAUSES, thmADD_AC]

thmADD1 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD1 = cacheProof "thmADD1" ctxtArith .
    prove [txt| !m. SUC m = m + 1 |] $
      tacREWRITE [thmBIT1_THM, thmADD_CLAUSES]

thmMULT_CLAUSES :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_CLAUSES = Base.thmMULT_CLAUSES

thmLT_IMP_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_IMP_LE = cacheProof "thmLT_IMP_LE" ctxtArith .
    prove [txt| !m n. m < n ==> m <= n |] $
      tacREWRITE [thmLT_LE] `_THEN` _REPEAT tacSTRIP `_THEN` 
      tacASM_REWRITE_NIL

thmLE_ADD_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD_RCANCEL = cacheProof "thmLE_ADD_RCANCEL" ctxtArith .
    prove [txt| !m n p. (m + p) <= (n + p) <=> (m <= n) |] $
      tacONCE_REWRITE [thmADD_SYM] `_THEN` 
      tacMATCH_ACCEPT thmLE_ADD_LCANCEL

thmLTE_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_ADD2 = cacheProof "thmLTE_ADD2" ctxtArith .
    prove [txt| !m n p q. m < p /\ n <= q ==> m + n < p + q |] $
      tacONCE_REWRITE [thmADD_SYM, thmCONJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLET_ADD2

thmMULT_SYM :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_SYM = Base.thmMULT_SYM

thmLEFT_ADD_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmLEFT_ADD_DISTRIB = Base.thmLEFT_ADD_DISTRIB

thmLE_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT_LCANCEL = cacheProof "thmLE_MULT_LCANCEL" ctxtArith $
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [txt| !m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                         , thmLE_REFL, thmLE_0, thmNOT_SUC ] `_THEN`
         tacREWRITE [thmLE_SUC] `_THEN`
         tacREWRITE [ defLE, thmLE_ADD_LCANCEL, ruleGSYM thmADD_ASSOC ] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmLT_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_MULT_LCANCEL = cacheProof "thmLT_MULT_LCANCEL" ctxtArith $
    do cths <- ruleCONJUNCTS thmMULT_CLAUSES
       prove [txt| !m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p |] $
         _REPEAT tacINDUCT `_THEN`
         tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                        , thmLT_REFL, thmLT_0, thmNOT_SUC] `_THEN`
         tacREWRITE [thmLT_SUC] `_THEN`
         tacREWRITE [ defLT, thmLT_ADD_LCANCEL, ruleGSYM thmADD_ASSOC ] `_THEN`
         tacASM_REWRITE [ruleGSYM (cths !! 4), thmNOT_SUC]

thmMULT_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_EQ_0 = cacheProof "thmMULT_EQ_0" ctxtArith .
    prove [txt| !m n. (m * n = 0) <=> (m = 0) \/ (n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES, thmNOT_SUC]

thmEQ_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_MULT_LCANCEL = cacheProof "thmEQ_MULT_LCANCEL" ctxtArith .
    prove [txt| !m n p. (m * n = m * p) <=> (m = 0) \/ (n = p) |] $
      tacINDUCT `_THEN` tacREWRITE [thmMULT_CLAUSES, thmNOT_SUC] `_THEN`
      _REPEAT tacINDUCT `_THEN`
      tacASM_REWRITE [ thmMULT_CLAUSES, thmADD_CLAUSES
                     , ruleGSYM thmNOT_SUC, thmNOT_SUC ] `_THEN`
      tacASM_REWRITE [thmSUC_INJ, ruleGSYM thmADD_ASSOC, thmEQ_ADD_LCANCEL]

thmEVEN_MULT :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_MULT = cacheProof "thmEVEN_MULT" ctxtArith .
    prove [txt| !m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n) |] $
      tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmMULT_CLAUSES, thmEVEN_ADD, defEVEN ] `_THEN`
      tacX_GEN [txt| p:num |] `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC [txt| n:num |] thmEVEN_OR_ODD) `_THEN`
      _DISJ_CASES_THEN tacMP (ruleSPEC [txt| p:num |] thmEVEN_OR_ODD) `_THEN`
      tacREWRITE [ruleGSYM thmNOT_EVEN] `_THEN` tacDISCH `_THEN`
      tacASM_REWRITE_NIL

thmEXP_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_EQ_0 = cacheProof "thmEXP_EQ_0" ctxtArith .
     prove [txt| !m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0) |] $
      _REPEAT tacINDUCT `_THEN` 
      tacASM_REWRITE [ thmBIT1_THM, thmNOT_SUC, defEXP
                     , thmMULT_CLAUSES, thmADD_CLAUSES, thmADD_EQ_0 ]

thmLT_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD2 = cacheProof "thmLT_ADD2" ctxtArith .
    prove [txt| !m n p q. m < p /\ n < q ==> m + n < p + q |] $
      _REPEAT tacSTRIP `_THEN` tacMATCH_MP thmLTE_ADD2 `_THEN`
      tacASM_REWRITE_NIL `_THEN` tacMATCH_MP thmLT_IMP_LE `_THEN`
      tacASM_REWRITE_NIL

thmRIGHT_ADD_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmRIGHT_ADD_DISTRIB = Base.thmRIGHT_ADD_DISTRIB

thmLEFT_SUB_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmLEFT_SUB_DISTRIB = cacheProof "thmLEFT_SUB_DISTRIB" ctxtArith .
    prove [txt| !m n p. m * (n - p) = m * n - m * p |] $
      _REPEAT tacGEN `_THEN` tacCONV convSYM `_THEN`
      tacDISJ_CASES (ruleSPECL [ [txt| n:num |]
                               , [txt| p:num |] ] thmLE_CASES) `_THENL`
      [ _FIRST_ASSUM 
          (\ th -> tacREWRITE [ruleREWRITE [ruleGSYM thmSUB_EQ_0] th])`_THEN`
        tacASM_REWRITE [thmMULT_CLAUSES, thmSUB_EQ_0, thmLE_MULT_LCANCEL]
      , _POP_ASSUM (_CHOOSE_THEN tacSUBST1 . ruleREWRITE [thmLE_EXISTS]) `_THEN`
        tacREWRITE [thmLEFT_ADD_DISTRIB] `_THEN`
        tacREWRITE [ruleONCE_REWRITE [thmADD_SYM] thmADD_SUB]
      ]

thmEVEN_DOUBLE :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_DOUBLE = cacheProof "thmEVEN_DOUBLE" ctxtArith .
    prove [txt| !n. EVEN(2 * n) |] $
      tacGEN `_THEN` tacREWRITE [thmEVEN_MULT] `_THEN` tacDISJ1 `_THEN`
      tacPURE_REWRITE [thmBIT0_THM, thmBIT1_THM] `_THEN` 
      tacREWRITE [defEVEN, thmEVEN_ADD]

thmLE_MULT_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT_RCANCEL = cacheProof "thmLE_MULT_RCANCEL" ctxtArith .
    prove [txt| !m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0) |] $
      tacONCE_REWRITE [thmMULT_SYM, thmDISJ_SYM] `_THEN`
      tacMATCH_ACCEPT thmLE_MULT_LCANCEL

thmDIVMOD_EXIST :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST = Base.thmDIVMOD_EXIST

thmMULT_2 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_2 = cacheProof "thmMULT_2" ctxtArith .
    prove [txt| !n. 2 * n = n + n |] $
      tacGEN `_THEN` 
      tacREWRITE [thmBIT0_THM, thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmARITH_MULT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_MULT = cacheProof "thmARITH_MULT" ctxtArith .
    prove [txt| (!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\
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

thmMULT_ASSOC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_ASSOC = cacheProof "thmMULT_ASSOC" ctxtArith .
    prove [txt| !m n p. m * (n * p) = (m * n) * p |] $
      tacINDUCT `_THEN` tacASM_REWRITE [thmMULT_CLAUSES, thmRIGHT_ADD_DISTRIB]

thmLE_MULT2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT2 = cacheProof "thmLE_MULT2" ctxtArith .
    prove [txt| !m n p q. m <= n /\ p <= q ==> m * p <= n * q |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [thmLE_EXISTS] `_THEN`
      _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE [txt| a:num |]) 
                     (tacX_CHOOSE [txt| b:num |])) `_THEN`
      tacEXISTS [txt| a * p + m * b + a * b |] `_THEN`
      tacASM_REWRITE [thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB, thmADD_ASSOC]

thmRIGHT_SUB_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmRIGHT_SUB_DISTRIB = cacheProof "thmRIGHT_SUB_DISTRIB" ctxtArith .
    prove [txt| !m n p. (m - n) * p = m * p - n * p |] $
      tacONCE_REWRITE [thmMULT_SYM] `_THEN` tacMATCH_ACCEPT thmLEFT_SUB_DISTRIB

thmARITH_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_LE = cacheProof "thmARITH_LE" ctxtArith $
    prove [txt| (!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\
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
                 , ruleDENUMERAL $ ruleGSYM thmNOT_SUC
                 , thmSUC_INJ ] `_THEN`
      tacREWRITE [ruleDENUMERAL thmLE_0] `_THEN` 
      tacREWRITE [ ruleDENUMERAL defLE
                 , ruleGSYM thmMULT_2 ] `_THEN`
      tacREWRITE [ thmLE_MULT_LCANCEL, thmSUC_INJ, ruleDENUMERAL thmMULT_EQ_0
                 , ruleDENUMERAL thmNOT_SUC ] `_THEN`
      tacREWRITE [ruleDENUMERAL thmNOT_SUC] `_THEN` 
      tacREWRITE [thmLE_SUC_LT] `_THEN`
      tacREWRITE [thmLT_MULT_LCANCEL] `_THEN`
      _SUBGOAL_THEN [txt| 2 = SUC 1 |] (\ th -> tacREWRITE [th]) `_THENL`
      [ tacREWRITE [ defNUMERAL, thmBIT0, thmBIT1
                   , ruleDENUMERAL thmADD_CLAUSES ]
      , tacREWRITE [ ruleDENUMERAL thmNOT_SUC
                   , thmNOT_SUC, thmEQ_MULT_LCANCEL ] `_THEN`
        tacREWRITE [ruleONCE_REWRITE [thmDISJ_SYM] thmLE_LT] `_THEN`
        _MAP_EVERY tacX_GEN [[txt| m:num |], [txt| n:num |]] `_THEN`
        _SUBGOAL_THEN [txt| ~(SUC 1 * m = SUC (SUC 1 * n)) |] 
          (\ th -> tacREWRITE [th]) `_THEN`
        _DISCH_THEN (tacMP . ruleAP_TERM [txt| EVEN |]) `_THEN`
        tacREWRITE [ thmEVEN_MULT, thmEVEN_ADD, defNUMERAL, thmBIT1
                   , defEVEN ]
      ]

thmMULT_AC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_AC = cacheProof "thmMULT_AC" ctxtArith .
    prove [txt| (m * n = n * m) /\
                ((m * n) * p = m * (n * p)) /\
                (m * (n * p) = n * (m * p)) |] $
      tacMESON [thmMULT_ASSOC, thmMULT_SYM]

thmARITH_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_LT = cacheProof "thmARITH_LT" ctxtArith .
    prove [txt| (!m n. NUMERAL m < NUMERAL n <=> m < n) /\
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

thmARITH_GE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_GE = cacheProof "thmARITH_GE" ctxtArith $
    ruleREWRITE [defGE, defGT] thmARITH_LE

thmARITH_EQ :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EQ = cacheProof "thmARITH_EQ" ctxtArith .
    prove [txt| (!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\
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

thmEXP_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_ADD = cacheProof "thmEXP_ADD" ctxtArith .
    prove [txt| !m n p. m EXP (n + p) = (m EXP n) * (m EXP p) |] $
      tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN`
      tacASM_REWRITE [ defEXP, thmADD_CLAUSES, thmMULT_CLAUSES, thmMULT_AC ]

thmDIVMOD_EXIST_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST_0 = Base.thmDIVMOD_EXIST_0

thmONE :: ArithCtxt thry => HOL cls thry HOLThm
thmONE = cacheProof "thmONE" ctxtArith $
    prove [txt| 1 = SUC 0 |] $ 
      tacREWRITE [thmBIT1, ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL]

thmTWO :: ArithCtxt thry => HOL cls thry HOLThm
thmTWO = cacheProof "thmTWO" ctxtArith $
    prove [txt| 2 = SUC 1 |] $ 
      tacREWRITE [ thmBIT0, thmBIT1
                 , ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL ]

thmARITH_GT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_GT = cacheProof "thmARITH_GT" ctxtArith $
    ruleREWRITE [ruleGSYM defGE, ruleGSYM defGT] thmARITH_LT

thmARITH_SUB :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_SUB = cacheProof "thmARITH_SUB" ctxtArith .
    prove [txt| (!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
                (_0 - _0 = _0) /\
                (!n. _0 - BIT0 n = _0) /\
                (!n. _0 - BIT1 n = _0) /\
                (!n. BIT0 n - _0 = BIT0 n) /\
                (!n. BIT1 n - _0 = BIT1 n) /\
                (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\
                (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\
                (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\
                (!m n. BIT1 m - BIT1 n = BIT0 (m - n)) |] $
      tacREWRITE [defNUMERAL, ruleDENUMERAL thmSUB_0] `_THEN`
      tacPURE_REWRITE [thmBIT0, thmBIT1] `_THEN`
      tacREWRITE [ ruleGSYM thmMULT_2, thmSUB_SUC, thmLEFT_SUB_DISTRIB ] `_THEN`
      tacREWRITE [defSUB] `_THEN` _REPEAT tacGEN `_THEN` tacCOND_CASES `_THEN`
      tacREWRITE [ruleDENUMERAL thmSUB_EQ_0] `_THEN`
      tacRULE_ASSUM (ruleREWRITE [thmNOT_LE]) `_THEN`
      tacASM_REWRITE [thmLE_SUC_LT, thmLT_MULT_LCANCEL, thmARITH_EQ] `_THEN`
      _POP_ASSUM (_CHOOSE_THEN tacSUBST1 . ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacREWRITE [thmADD1, thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmADD_SUB2, ruleGSYM thmADD_ASSOC]

thmARITH_EXP :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EXP = cacheProof "thmARITH_EXP" ctxtArith $
    prove [txt| (!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
                (_0 EXP _0 = BIT1 _0) /\
                (!m. (BIT0 m) EXP _0 = BIT1 _0) /\
                (!m. (BIT1 m) EXP _0 = BIT1 _0) /\
                (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\
                (!m n. (BIT0 m) EXP (BIT0 n) = 
                       ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
                (!m n. (BIT1 m) EXP (BIT0 n) = 
                       ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\
                (!n. _0 EXP (BIT1 n) = _0) /\
                (!m n. (BIT0 m) EXP (BIT1 n) =
                       BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
                (!m n. (BIT1 m) EXP (BIT1 n) =
                       BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) |] $
      tacREWRITE [defNUMERAL] `_THEN` _REPEAT tacSTRIP `_THEN`
      _TRY (tacGEN_REWRITE (convLAND . convRAND) [thmBIT0, thmBIT1]) `_THEN`
      tacREWRITE [ ruleDENUMERAL defEXP, ruleDENUMERAL thmMULT_CLAUSES
                 , thmEXP_ADD ]

thmARITH_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_0 = cacheProof "thmARITH_0" ctxtArith $
    ruleMESON [defNUMERAL, thmADD_CLAUSES] [txt| m + _0 = m /\ _0 + n = n |]

thmBITS_INJ :: ArithCtxt thry => HOL cls thry HOLThm
thmBITS_INJ = cacheProof "thmBITS_INJ" ctxtArith .
    prove [txt| (BIT0 m = BIT0 n <=> m = n) /\
                (BIT1 m = BIT1 n <=> m = n) |] $
      tacREWRITE [thmBIT0, thmBIT1] `_THEN`
      tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
      tacREWRITE [thmSUC_INJ, thmEQ_MULT_LCANCEL, thmARITH_EQ]

thmSUB_ELIM :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_ELIM = cacheProof "thmSUB_ELIM" ctxtArith $
    prove [txt| P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d |] $
      tacDISJ_CASES (ruleSPECL [ [txt| a:num |]
                               , [txt| b:num |] ] thmLTE_CASES) `_THENL`
      [ tacASM_MESON [thmNOT_LT, thmSUB_EQ_0, thmLT_IMP_LE, thmLE_ADD]
      , _ALL
      ] `_THEN`
      _FIRST_ASSUM (_X_CHOOSE_THEN [txt| e:num |] tacSUBST1 . 
                     ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacSIMP [ thmADD_SUB2, ruleGSYM thmNOT_LE
              , thmLE_ADD, thmEQ_ADD_LCANCEL ] `_THEN` 
      tacMESON_NIL

thmEXP_2 :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_2 = cacheProof "thmEXP_2" ctxtArith .
    prove [txt| !n. n EXP 2 = n * n |] $
      tacREWRITE [ thmBIT0_THM, thmBIT1_THM, defEXP
                 , thmEXP_ADD, thmMULT_CLAUSES, thmADD_CLAUSES ]

convNUM_CANCEL :: ArithCtxt thry => Conversion cls thry
convNUM_CANCEL = Conv $ \ tm ->
    do tmAdd <- serve [arith| (+) |]
       tmeq <- serve [arith| (=) :num->num->bool |]
       (l, r) <- destEq tm
       let lats = sort (<=) $ binops tmAdd l
           rats = sort (<=) $ binops tmAdd r
           (i, lats', rats') = minter [] [] [] lats rats
       l' <- listMkBinop tmAdd (i ++ lats')
       r' <- listMkBinop tmAdd (i ++ rats')
       lth <- ruleAC =<< mkEq l l'
       rth <- ruleAC =<< mkEq r r'
       eth <- primMK_COMB (ruleAP_TERM tmeq lth) rth
       ruleGEN_REWRITE (convRAND . _REPEAT) 
         [thmEQ_ADD_LCANCEL, thmEQ_ADD_LCANCEL_0, convNUM_CANCEL_pth] eth
  where minter :: [HOLTerm] -> [HOLTerm] -> [HOLTerm] -> [HOLTerm] -> [HOLTerm] 
               -> ([HOLTerm], [HOLTerm], [HOLTerm])
        minter i l1' l2' [] l2 = (i, l1', l2' ++ l2)
        minter i l1' l2' l1 [] = (i, l1 ++ l1', l2')
        minter i l1' l2' l1@(h1:t1) l2@(h2:t2)
            | h1 == h2 = minter (h1:i) l1' l2' t1 t2
            | h1 < h2 = minter i (h1:l1') l2' t1 l2
            | otherwise = minter i l1' (h2:l2') l1 t2

        ruleAC :: ArithCtxt thry => HOLTerm 
               -> HOL cls thry HOLThm
        ruleAC = runConv (convAC thmADD_AC)
            
        convNUM_CANCEL_pth :: ArithCtxt thry 
                           => HOL cls thry HOLThm
        convNUM_CANCEL_pth = cacheProof "convNUM_CANCEL_pth" ctxtArith $
            ruleGEN_REWRITE (funpow 2 convBINDER . convLAND) [thmEQ_SYM_EQ] 
              thmEQ_ADD_LCANCEL_0

ruleLE_IMP :: (ArithCtxt thry, HOLThmRep thm cls thry) => thm 
           -> HOL cls thry HOLThm
ruleLE_IMP th =
    ruleGEN_ALL . ruleMATCH_MP ruleLE_IMP_pth $ ruleSPEC_ALL th
  where ruleLE_IMP_pth :: ArithCtxt thry 
                       => HOL cls thry HOLThm
        ruleLE_IMP_pth = cacheProof "ruleLE_IMP_pth" ctxtArith $
            rulePURE_ONCE_REWRITE [thmIMP_CONJ] thmLE_TRANS

thmDIVISION :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVISION = cacheProof "thmDIVISION" ctxtArith .
    prove [txt| !m n. ~(n = 0) ==> 
                      (m = m DIV n * n + m MOD n) /\ m MOD n < n |] $
      tacMESON [specDIVISION_0]
