module HaskHOL.Lib.CalcNum.Pre where

import HaskHOL.Core hiding (base)
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF.Context


-- Build up lookup table for numeral conversions.
tmZero', tmBIT0', tmBIT1', tmM', tmN', tmP', tmAdd', tmSuc' :: WFCtxt thry => PTerm thry
tmZero' = [wF| _0 |]
tmBIT0' = [wF| BIT0 |]
tmBIT1' = [wF| BIT1 |]
tmM' = [wF| m:num |]
tmN' = [wF| n:num |]
tmP' = [wF| p:num |]
tmAdd' = [wF| (+) |]
tmSuc' = [wF| SUC |]


mkClauses :: (BasicConvs thry, WFCtxt thry) => Bool -> HOLTerm 
          -> HOL cls thry (HOLThm, Int)
mkClauses sucflag t =
    do tmSuc <- serve tmSuc'
       tmAdd <- serve tmAdd'
       tmM <- serve tmM'
       tmP <- serve tmP'
       let tm = if sucflag then fromRight $ mkComb tmSuc t else t
       th1 <- runConv (convPURE_REWRITE 
                         [thmARITH_ADD, thmARITH_SUC, thmARITH_0]) tm
       tm1 <- patadj #<< rand (concl th1)
       if not (tmAdd `freeIn` tm1)
          then return (th1, if tmM `freeIn` tm1 then 0 else 1)
          else let ptm = fromJust $ rand =<< rand =<< rand =<< 
                                      rand tm1 in
                 do tmc <- liftM1 mkEq (mkEq ptm tmP) =<< mkEq tm #<<
                             subst [(ptm, tmP)] tm1
                    th <- ruleEQT_ELIM =<< 
                            runConv (convREWRITE [ thmARITH_ADD
                                                 , thmARITH_SUC
                                                 , thmARITH_0
                                                 , thmBITS_INJ]) tmc
                    return (th, if tmSuc `freeIn` tm1 then 3 else 2)
  where patadj :: HOLTerm -> HOL cls thry HOLTerm
        patadj tm = 
            do tms <- mapM (pairMapM toHTm) [("SUC m", "SUC (m + _0)"), ("SUC n", "SUC (_0 + n)")]
               liftO $ subst tms tm

starts :: WFCtxt thry => HOL cls thry [HOLTerm]
starts = 
    do tmM <- serve tmM'
       tmN <- serve tmN'
       tmAdd <- serve tmAdd'
       ms <- bases tmM
       ns <- bases tmN
       return $! allpairsV (\ mtm ntm -> fromRight $
                   flip mkComb ntm =<< mkComb tmAdd mtm) ms ns
  where allpairsV :: (a -> b -> c) -> [a] -> [b] -> [c]
        allpairsV _ [] _ = []
        allpairsV f (h:t) ys =
            foldr (\ x a -> f h x : a) (allpairsV f t ys) ys
            
       
        bases :: WFCtxt thry => HOLTerm -> HOL cls thry [HOLTerm]
        bases v =
            do tmBIT1 <- serve tmBIT1'
               tmBIT0 <- serve tmBIT0'
               tmZero <- serve tmZero'
               let v0 = fromRight $ mkComb tmBIT0 v
                   v1 = fromRight $ mkComb tmBIT1 v
               part2 <- mapM (`mkCompnumeral` v) [8..15]
               part1 <- mapM (liftO . subst [(v1, v0)]) part2
               part0 <- mapM (`mkCompnumeral` tmZero) [0..15]
               return $! part0 ++ part1 ++ part2

        mkCompnumeral :: WFCtxt thry => Int -> HOLTerm -> HOL cls thry HOLTerm
        mkCompnumeral 0 base = return base
        mkCompnumeral k base =
            do tmBIT1 <- serve tmBIT1'
               tmBIT0 <- serve tmBIT0'
               t <- mkCompnumeral (k `div` 2) base
               liftO $ if k `mod` 2 == 1
                       then mkComb tmBIT1 t
                       else mkComb tmBIT0 t

convNUM_SHIFT_pths1' :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
convNUM_SHIFT_pths1' = cacheProof "convNUM_SHIFT_pths1'" ctxtWF .
    prove [str| (n = a + p * b <=>
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
      tacABBREV "two = 2" `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
      tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                 , thmEQ_MULT_LCANCEL, thmARITH_EQ
                 , ruleGSYM thmLEFT_ADD_DISTRIB, ruleGSYM thmMULT_ASSOC ]

convNUM_SHIFT_pths0' :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
convNUM_SHIFT_pths0' = cacheProof "convNUM_SHIFT_pths0'" ctxtWF .
    prove [str| (n = _0 + p * b <=>
                 BIT0(BIT0(BIT0(BIT0 n))) =
                 _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT0(BIT0(BIT0 n))) =
                 BIT1 _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT1(BIT0(BIT0 n))) =
                 BIT0(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT1(BIT0(BIT0 n))) =
                 BIT1(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT0(BIT1(BIT0 n))) =
                 BIT0(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT0(BIT1(BIT0 n))) =
                 BIT1(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT1(BIT1(BIT0 n))) =
                 BIT0(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT1(BIT1(BIT0 n))) =
                 BIT1(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT0(BIT0(BIT1 n))) =
                 BIT0(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT0(BIT0(BIT1 n))) =
                 BIT1(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT1(BIT0(BIT1 n))) =
                 BIT0(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT1(BIT0(BIT1 n))) =
                 BIT1(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT0(BIT1(BIT1 n))) =
                 BIT0(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT0(BIT1(BIT1 n))) =
                 BIT1(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT0(BIT1(BIT1(BIT1 n))) =
                 BIT0(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\
                (n = _0 + p * b <=>
                 BIT1(BIT1(BIT1(BIT1 n))) =
                 BIT1(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) |] $
      tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT0) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT1) `_THEN`
      tacABBREV "two = 2" `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
      tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                 , thmEQ_MULT_LCANCEL, thmARITH_EQ
                 , ruleGSYM thmLEFT_ADD_DISTRIB, ruleGSYM thmMULT_ASSOC ]

convNUM_UNSHIFT_puths1' :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
convNUM_UNSHIFT_puths1' = cacheProof "convNUM_UNSHIFT_puths1'" ctxtWF .
    prove [str| (a + p * b = n <=>
                 BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT0(BIT0(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT0(BIT0(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT1(BIT0(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT1(BIT0(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT0(BIT1(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT0(BIT1(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT1(BIT1(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT1(BIT1(BIT0 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT0(BIT0(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT0(BIT0(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT1(BIT0(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT1(BIT0(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT0(BIT1(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT0(BIT1(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT0(BIT1(BIT1(BIT1 n)))) /\
                (a + p * b = n <=>
                 BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =
                 BIT1(BIT1(BIT1(BIT1 n)))) |] $
      tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT0) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT1) `_THEN`
      tacABBREV "two = 2" `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE[th]) `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE[th]) `_THEN`
      _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
      tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                 , thmEQ_MULT_LCANCEL, thmARITH_EQ
                 , ruleGSYM thmLEFT_ADD_DISTRIB
                 , ruleGSYM thmMULT_ASSOC
                 ]
