{-# LANGUAGE PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.Arith
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Arith 
    ( ArithType
    , ArithCtxt
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
    , thmADD_0 -- stage2
    , thmADD_SUC
    , thmLE_SUC_LT
    , thmLT_SUC_LE
    , thmLE_0
    , wfNUM'
    , thmSUB_0
    , thmSUB_PRESUC
    , thmLE_REFL
    , thmNOT_EVEN
    , thmNOT_ODD
    , thmADD_CLAUSES -- stage3
    , thmLE_SUC
    , thmLT_SUC
    , wopNUM
    , thmSUB_SUC
    , thmEVEN_OR_ODD
    , thmEVEN_AND_ODD
    , thmLET_CASES
    , thmEQ_IMP_LE
    , thmADD_SYM -- stage4
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
    , thmBIT0_THM -- stage5
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
    , thmBIT1_THM -- stage6
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
    , thmADD1 -- stage7
    , thmMULT_CLAUSES
    , thmLT_IMP_LE
    , thmLE_ADD_RCANCEL
    , thmLTE_ADD2
    , thmMULT_SYM -- stage8
    , thmLEFT_ADD_DISTRIB
    , thmLE_MULT_LCANCEL
    , thmLT_MULT_LCANCEL
    , thmMULT_EQ_0
    , thmEQ_MULT_LCANCEL
    , thmEVEN_MULT
    , thmEXP_EQ_0
    , thmLT_ADD2
    , thmRIGHT_ADD_DISTRIB -- stage9
    , thmLEFT_SUB_DISTRIB
    , thmEVEN_DOUBLE
    , thmLE_MULT_RCANCEL
    , thmDIVMOD_EXIST -- stage10
    , thmMULT_2
    , thmDIVMOD_EXIST_0
    , specDIVISION_0
    , defMinimal
    , thmARITH_MULT
    , thmMULT_ASSOC
    , thmLE_MULT2
    , thmRIGHT_SUB_DISTRIB
    , thmARITH_LE -- stage11
    , thmEXP_ADD
    , thmMULT_AC
    , thmARITH_LT -- stage12
    , thmARITH_GE
    , thmARITH_EQ
    , thmONE -- here
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
import HaskHOL.Deductive hiding (getSpecification)

import HaskHOL.Lib.Nums

import HaskHOL.Lib.Arith.Base
import HaskHOL.Lib.Arith.Context
       
specDIVISION_0 :: ArithCtxt thry => HOL cls thry HOLThm
specDIVISION_0 = cacheProof "specDIVISION_0" ctxtArith $ 
    getSpecification ["DIV", "MOD"]

defMinimal :: ArithCtxt thry => HOL cls thry HOLThm
defMinimal = cacheProof "defMinimal" ctxtArith $ getDefinition "minimal"


thmONE :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmONE = cacheProof "thmONE" ctxtArith $
    prove "1 = SUC 0" $ 
      tacREWRITE [thmBIT1, ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL]

thmTWO :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmTWO = cacheProof "thmTWO" ctxtArith $
    prove "2 = SUC 1" $ 
      tacREWRITE [ thmBIT0, thmBIT1
                 , ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL ]

thmARITH_GT :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmARITH_GT = cacheProof "thmARITH_GT" ctxtArith $
    ruleREWRITE [ruleGSYM defGE, ruleGSYM defGT] thmARITH_LT

thmARITH_SUB :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmARITH_SUB = cacheProof "thmARITH_SUB" ctxtArith .
    prove [str| (!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
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

thmARITH_EXP :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmARITH_EXP = cacheProof "thmARITH_EXP" ctxtArith $
    prove [str| (!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
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

thmARITH_0 :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmARITH_0 = cacheProof "thmARITH_0" ctxtArith $
    ruleMESON [defNUMERAL, thmADD_CLAUSES] [str| m + _0 = m /\ _0 + n = n |]

thmBITS_INJ :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmBITS_INJ = cacheProof "thmBITS_INJ" ctxtArith .
    prove [str| (BIT0 m = BIT0 n <=> m = n) /\
                (BIT1 m = BIT1 n <=> m = n) |] $
      tacREWRITE [thmBIT0, thmBIT1] `_THEN`
      tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
      tacREWRITE [thmSUC_INJ, thmEQ_MULT_LCANCEL, thmARITH_EQ]

thmSUB_ELIM :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmSUB_ELIM = cacheProof "thmSUB_ELIM" ctxtArith $
    prove [str| P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d |] $
      tacDISJ_CASES (ruleSPECL ["a:num", "b:num"] =<< thmLTE_CASES) `_THENL`
      [ tacASM_MESON [thmNOT_LT, thmSUB_EQ_0, thmLT_IMP_LE, thmLE_ADD]
      , _ALL
      ] `_THEN`
      _FIRST_ASSUM (_X_CHOOSE_THEN "e:num" tacSUBST1 . 
                     ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacSIMP [ thmADD_SUB2, ruleGSYM thmNOT_LE
              , thmLE_ADD, thmEQ_ADD_LCANCEL ] `_THEN` 
      tacMESON_NIL

thmEXP_2 :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmEXP_2 = cacheProof "thmEXP_2" ctxtArith .
    prove "!n. n EXP 2 = n * n" $
      tacREWRITE [ thmBIT0_THM, thmBIT1_THM, defEXP
                 , thmEXP_ADD, thmMULT_CLAUSES, thmADD_CLAUSES ]

convNUM_CANCEL :: (BasicConvs thry, ArithCtxt thry) => Conversion cls thry
convNUM_CANCEL = Conv $ \ tm ->
    do tmAdd <- serve [arith| (+) |]
       tmeq <- serve [arith| (=) :num->num->bool |]
       let (l, r) = fromJust $ destEq tm
           lats = sort (<=) $ binops tmAdd l
           rats = sort (<=) $ binops tmAdd r
           (i, lats', rats') = minter [] [] [] lats rats
       let l' = fromRight $ listMkBinop tmAdd (i ++ lats')
           r' = fromRight $ listMkBinop tmAdd (i ++ rats')
       lth <- ruleAC =<< mkEq l l'
       rth <- ruleAC =<< mkEq r r'
       let eth = fromRight $ liftM1 primMK_COMB (ruleAP_TERM tmeq lth) rth
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

        ruleAC :: (BasicConvs thry, ArithCtxt thry) => HOLTerm 
               -> HOL cls thry HOLThm
        ruleAC = runConv (convAC thmADD_AC)
            
        convNUM_CANCEL_pth :: (BasicConvs thry, ArithCtxt thry) 
                           => HOL cls thry HOLThm
        convNUM_CANCEL_pth = cacheProof "convNUM_CANCEL_pth" ctxtArith $
            ruleGEN_REWRITE (funpow 2 convBINDER . convLAND) 
              [thmEQ_SYM_EQ] =<< thmEQ_ADD_LCANCEL_0

ruleLE_IMP :: (BasicConvs thry, ArithCtxt thry, HOLThmRep thm cls thry) => thm 
           -> HOL cls thry HOLThm
ruleLE_IMP th =
    ruleGEN_ALL =<< ruleMATCH_MP ruleLE_IMP_pth =<< ruleSPEC_ALL th
  where ruleLE_IMP_pth :: (BasicConvs thry, ArithCtxt thry) 
                       => HOL cls thry HOLThm
        ruleLE_IMP_pth = cacheProof "ruleLE_IMP_pth" ctxtArith $
            rulePURE_ONCE_REWRITE[thmIMP_CONJ] =<< thmLE_TRANS

thmDIVISION :: (BasicConvs thry, ArithCtxt thry) => HOL cls thry HOLThm
thmDIVISION = cacheProof "thmDIVISION" ctxtArith .
    prove [str| !m n. ~(n = 0) ==> 
                      (m = m DIV n * n + m MOD n) /\ m MOD n < n |] $
      tacMESON [specDIVISION_0]
