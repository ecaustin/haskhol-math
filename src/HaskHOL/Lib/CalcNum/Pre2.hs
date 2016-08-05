{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, TemplateHaskell,
             TypeFamilies #-}
module HaskHOL.Lib.CalcNum.Pre2 where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF

import HaskHOL.Lib.CalcNum.Pre

thmARITH :: WFCtxt thry => HOL cls thry HOLThm
thmARITH = cacheProof "thmARITH" ctxtWF $ foldr1M ruleCONJ =<< 
    sequence [ thmARITH_ZERO, thmARITH_SUC, thmARITH_PRE
             , thmARITH_ADD, thmARITH_MULT, thmARITH_EXP
             , thmARITH_EVEN, thmARITH_ODD, thmARITH_EQ
             , thmARITH_LE, thmARITH_LT, thmARITH_GE
             , thmARITH_GT, thmARITH_SUB
             ]

-- Lookup arrays for numeral conversions
addValues :: WFCtxt thry => HOL cls thry ([HOLThm], [Int])
addValues = serializeValue "addValues" ctxtWF $
  liftM unzip $ mapM (mkClauses False) =<< starts

addClauses :: WFCtxt thry => HOL cls thry [HOLThm]
addClauses = fst `fmap` addValues

addFlags :: WFCtxt thry => HOL cls thry [Int]
addFlags = snd `fmap` addValues

adcValues :: WFCtxt thry => HOL cls thry ([HOLThm], [Int])
adcValues = serializeValue "adcValues" ctxtWF $
  liftM unzip $ mapM (mkClauses True) =<< starts

adcClauses :: WFCtxt thry => HOL cls thry [HOLThm]
adcClauses = fst `fmap` adcValues

adcFlags :: WFCtxt thry => HOL cls thry [Int]
adcFlags = snd `fmap` adcValues

convNUM_SHIFT_pths1 :: WFCtxt thry => HOL cls thry [HOLThm]
convNUM_SHIFT_pths1 = serializeValue "convNUM_SHIFT_pths1" ctxtWF $
    ruleCONJUNCTS convNUM_SHIFT_pths1'
  where convNUM_SHIFT_pths1' :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pths1' = cacheProof "convNUM_SHIFT_pths1'" ctxtWF .
          prove 
            [txt| (n = a + p * b <=>
                   BIT0(BIT0(BIT0(BIT0 n))) =
                   BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT0(BIT0(BIT0 n))) =
                   BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT1(BIT0(BIT0 n))) =
                   BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT1(BIT0(BIT0 n))) =
                   BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT0(BIT1(BIT0 n))) =
                   BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT0(BIT1(BIT0 n))) =
                   BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT1(BIT1(BIT0 n))) =
                   BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT1(BIT1(BIT0 n))) =
                   BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT0(BIT0(BIT1 n))) =
                   BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT0(BIT0(BIT1 n))) =
                   BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT1(BIT0(BIT1 n))) =
                   BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT1(BIT0(BIT1 n))) =
                   BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT0(BIT1(BIT1 n))) =
                   BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT0(BIT1(BIT1 n))) =
                   BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT0(BIT1(BIT1(BIT1 n))) =
                   BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                  (n = a + p * b <=>
                   BIT1(BIT1(BIT1(BIT1 n))) =
                   BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) |] $
            tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT0) `_THEN`
            tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT1) `_THEN`
            tacABBREV [txt| two = 2 |] `_THEN`
            _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
            _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
            _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
            tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                       , thmEQ_MULT_LCANCEL, thmARITH_EQ
                       , ruleGSYM thmLEFT_ADD_DISTRIB, ruleGSYM thmMULT_ASSOC 
                       ]

convNUM_SHIFT_pths0 :: WFCtxt thry => HOL cls thry [HOLThm]
convNUM_SHIFT_pths0 = serializeValue "convNUM_SHIFT_pths0" ctxtWF $
    ruleCONJUNCTS convNUM_SHIFT_pths0'

convNUM_UNSHIFT_puths1 :: WFCtxt thry => HOL cls thry [HOLThm]
convNUM_UNSHIFT_puths1 = serializeValue "convNUM_UNSHIFT_puths1" ctxtWF $
    ruleCONJUNCTS convNUM_UNSHIFT_puths1'

convNUM_UNSHIFT_puths2 :: WFCtxt thry => HOL cls thry [HOLThm]
convNUM_UNSHIFT_puths2 = serializeValue "convNUM_UNSHIFT_puths1" ctxtWF $
    do puths <- convNUM_UNSHIFT_puths1
       mapM (\ i -> 
                 let th1 = puths !! (i `mod` 16)
                     th2 = puths !! (i `div` 16) in
                   ruleGEN_REWRITE convRAND [th1] th2) [0..256]
