module HaskHOL.Lib.CalcNum.Pre where

import HaskHOL.Core hiding (base)
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF

-- Build up lookup table for numeral conversions.
tmZero, tmBIT0, tmBIT1, tmM, tmN, tmP, tmAdd, tmSuc :: WFCtxt thry => HOL cls thry HOLTerm
tmZero = serve [wf| _0 |]
tmBIT0 = serve [wf| BIT0 |]
tmBIT1 = serve [wf| BIT1 |]
tmM = serve [wf| m:num |]
tmN = serve [wf| n:num |]
tmP = serve [wf| p:num |]
tmAdd = serve [wf| (+) |]
tmSuc = serve [wf| SUC |]

mkClauses :: WFCtxt thry => Bool -> HOLTerm -> HOL cls thry (HOLThm, Int)
mkClauses sucflag t =
    do tmSuc' <- tmSuc
       tm <- if sucflag then mkComb tmSuc' t else return t
       th1 <- runConv (convPURE_REWRITE 
                         [thmARITH_ADD, thmARITH_SUC, thmARITH_0]) tm
       tm1 <- patadj =<< rand (concl th1)
       tmAdd' <- toHTm tmAdd
       tmP' <- toHTm tmP
       tmM' <- toHTm tmM
       if not (tmAdd' `freeIn` tm1)
          then return (th1, if tmM' `freeIn` tm1 then 0 else 1)
          else do ptm <- rand =<< rand =<< rand =<< rand tm1
                  ptm' <- mkEq ptm tmP'
                  tmc <- mkEq ptm' =<< mkEq tm =<< subst [(ptm, tmP')] tm1
                  th <- ruleEQT_ELIM =<< 
                          runConv (convREWRITE [ thmARITH_ADD
                                               , thmARITH_SUC
                                               , thmARITH_0
                                               , thmBITS_INJ]) tmc
                  return (th, if tmSuc' `freeIn` tm1 then 3 else 2)
  where patadj :: WFCtxt thry => HOLTerm -> HOL cls thry HOLTerm
        patadj tm = 
            do tms <- mapM (pairMapM toHTm) 
                        [ (serve [wf| SUC m |], serve [wf| SUC (m + _0) |])
                        , (serve [wf| SUC n |], serve [wf| SUC (_0 + n) |])]
               subst tms tm

starts :: WFCtxt thry => HOL cls thry [HOLTerm]
starts = 
    do ms <- bases tmM
       ns <- bases tmN
       allpairsV (\ mtm ntm -> mkComb (mkComb tmAdd mtm) ntm) ms ns
  where allpairsV :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
        allpairsV _ [] _ = return []
        allpairsV f (h:t) ys =
            do t' <- allpairsV f t ys
               foldrM (\ x a -> do h' <- f h x
                                   return (h' : a)) t' ys
            
       
        bases :: (WFCtxt thry, HOLTermRep tm cls thry) 
              => tm -> HOL cls thry [HOLTerm]
        bases pv =
            do v <- toHTm pv
               v0 <- mkComb tmBIT0 v
               v1 <- mkComb tmBIT1 v
               part2 <- mapM (`mkCompnumeral` v) [8..15]
               part1 <- mapM (subst [(v1, v0)]) part2
               tmZero' <- toHTm tmZero
               part0 <- mapM (`mkCompnumeral` tmZero') [0..15]
               return $! part0 ++ part1 ++ part2

        mkCompnumeral :: WFCtxt thry => Int -> HOLTerm -> HOL cls thry HOLTerm
        mkCompnumeral 0 base = return base
        mkCompnumeral k base =
            do t <- mkCompnumeral (k `div` 2) base
               if k `mod` 2 == 1
                  then mkComb tmBIT1 t
                  else mkComb tmBIT0 t


convNUM_SHIFT_pths0' :: WFCtxt thry => HOL cls thry HOLThm
convNUM_SHIFT_pths0' = cacheProof "convNUM_SHIFT_pths0'" ctxtWF .
    prove [txt| (n = _0 + p * b <=>
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
      tacSUBST1 (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT0) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT1) `_THEN`
      tacABBREV [txt| two = 2 |] `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE [th]) `_THEN`
      _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
      tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                 , thmEQ_MULT_LCANCEL, thmARITH_EQ
                 , ruleGSYM thmLEFT_ADD_DISTRIB, ruleGSYM thmMULT_ASSOC ]

convNUM_UNSHIFT_puths1' :: WFCtxt thry => HOL cls thry HOLThm
convNUM_UNSHIFT_puths1' = cacheProof "convNUM_UNSHIFT_puths1'" ctxtWF .
    prove [txt| (a + p * b = n <=>
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
      tacSUBST1 (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT0) `_THEN`
      tacMP (ruleREWRITE [ruleGSYM thmMULT_2] thmBIT1) `_THEN`
      tacABBREV [txt| two = 2 |] `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE[th]) `_THEN`
      _DISCH_THEN (\ th -> tacREWRITE[th]) `_THEN`
      _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
      tacREWRITE [ thmADD_CLAUSES, thmSUC_INJ
                 , thmEQ_MULT_LCANCEL, thmARITH_EQ
                 , ruleGSYM thmLEFT_ADD_DISTRIB
                 , ruleGSYM thmMULT_ASSOC
                 ]
