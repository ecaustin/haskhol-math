{-# LANGUAGE PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.CalcNum
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.CalcNum
    ( thmARITH
    , convNUM_EVEN
    , convNUM_SUC
    , convNUM_LE
    , convNUM_EQ
    , convNUM_ADD
    , convNUM_MULT
    , convNUM_EXP
    , convNUM_LT
    , convNUM
    , ruleNUM_ADC
    , adcClauses
    , adcFlags
    , topsplit
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF

import HaskHOL.Lib.CalcNum.Pre
import HaskHOL.Lib.CalcNum.Pre2

import qualified Data.Vector as V

tmA', tmB', tmC', tmD', tmE', tmH', tmL', tmMul' :: WFCtxt thry => PTerm thry
tmA' = [wF| a:num |]
tmB' = [wF| b:num |]
tmC' = [wF| c:num |]
tmD' = [wF| d:num |]
tmE' = [wF| e:num |]
tmH' = [wF| h:num |]
tmL' = [wF| l:num |]
tmMul' = [wF| (*) |]

-- numeral conversions
convNUM_EVEN :: WFCtxt thry => Conversion cls thry
convNUM_EVEN = Conv $ \ tm ->
    do (tth, rths) <- ruleCONJ_PAIR thmARITH_EVEN
       runConv (convGEN_REWRITE id [tth] `_THEN` convGEN_REWRITE id [rths]) tm

convNUM_SUC ::  WFCtxt thry => Conversion cls thry
convNUM_SUC = Conv $ \ tm ->
    case tm of
      (Comb SUC (NUMERAL mtm)) ->
          if wellformed mtm
          then do tmM <- serve tmM'
                  tmN <- serve tmN'
                  tmZero <- serve tmZero'
                  pth <- convNUM_SUC_pth
                  th1 <- ruleNUM_ADC tmZero mtm
                  let ntm = fromJust . rand $ concl th1
                  liftO $ primEQ_MP 
                          (fromJust $ primINST [(tmM, mtm), (tmN, ntm)] pth) th1
          else fail "convNUM_SUC: not wellformed."
      _ -> fail "convNUM_SUC"
  where convNUM_SUC_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SUC_pth = cacheProof "convNUM_SUC_pth" ctxtWF .
            prove "SUC(_0 + m) = n <=> SUC(NUMERAL m) = NUMERAL n" $
              tacBINOP `_THEN` tacMESON [defNUMERAL, thmADD_CLAUSES]

convNUM_ADD :: WFCtxt thry => Conversion cls thry
convNUM_ADD = Conv $ \ tm ->
    case tm of
      (Comb (Comb (Const "+" _) (NUMERAL mtm)) (NUMERAL ntm)) ->
          if wellformed mtm && wellformed ntm
          then do tmM <- serve tmM'
                  tmN <- serve tmN'
                  tmP <- serve tmP'
                  pth <- convNUM_ADD_pth
                  th1 <- ruleNUM_ADD mtm ntm
                  let ptm = fromJust . rand $ concl th1
                      th2 = fromJust $ primINST [ (tmM, mtm), (tmN, ntm)
                                                , (tmP, ptm) ] pth
                  liftO $ primEQ_MP th2 th1
          else fail "convNUM_ADD: not wellformed."
      _ -> fail "convNUM_ADD"
  where convNUM_ADD_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_ADD_pth = cacheProof "convNUM_ADD_pth" ctxtWF $
            ruleMESON [defNUMERAL] 
              "m + n = p <=> NUMERAL m + NUMERAL n = NUMERAL p"

convNUM_MULT :: WFCtxt thry => Conversion cls thry
convNUM_MULT = Conv $ \ tm ->
    case tm of
      (Comb (Comb (Const "*" _) (NUMERAL mtm)) (NUMERAL ntm)) ->
          if mtm == ntm
          then do tmM <- serve tmM'
                  tmP <- serve tmP'
                  pth <- convNUM_MULT_pth2
                  th1 <- ruleNUM_SQUARE mtm
                  let ptm = fromJust . rand $ concl th1
                  liftO $ primEQ_MP 
                          (fromJust $ primINST [(tmM, mtm), (tmP, ptm)] pth) th1
          else let (w1, z1) = fromJust $ bitcounts mtm
                   (w2, z2) = fromJust $ bitcounts ntm in
                 do tmM <- serve tmM'
                    tmN <- serve tmN'
                    tmP <- serve tmP'
                    pth <- convNUM_MULT_pth1
                    th1 <- ruleNUM_MUL (w1+z1) (w2+z2) mtm ntm
                    let ptm = fromJust . rand $ concl th1
                        th2 = fromJust $ primINST [ (tmM, mtm), (tmN, ntm)
                                                  , (tmP, ptm) ] pth
                    liftO $ primEQ_MP th2 th1
      _ -> fail "convNUM_MULT"
  where convNUM_MULT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_MULT_pth1 = cacheProof "convNUM_MULT_pth1" ctxtWF $
            ruleMESON [defNUMERAL] 
              "m * n = p <=> NUMERAL m * NUMERAL n = NUMERAL p"

        convNUM_MULT_pth2 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_MULT_pth2 = cacheProof "convNUM_MULT_pth2" ctxtWF $
            ruleMESON [defNUMERAL, thmEXP_2] 
              "m EXP 2 = p <=> NUMERAL m * NUMERAL m = NUMERAL p"

convNUM_LE :: WFCtxt thry => Conversion cls thry
convNUM_LE = Conv $ \ tm ->
    case tm of
      (Comb (Comb (Const "<=" _) (NUMERAL mtm)) (NUMERAL ntm)) ->
        let rel = orderrelation mtm ntm in
          if rel == Just EQ 
          then do pth <- convNUM_LE_rth
                  tmN <- serve tmN'
                  liftO $ primINST [(tmN, ntm)] pth
          else if rel == Just LT
               then do pth <- convNUM_LE_pth
                       tmM <- serve tmM'
                       tmN <- serve tmN'
                       tmP <- serve tmP'
                       dtm <- subbn ntm mtm
                       th <- ruleNUM_ADD dtm mtm
                       liftO $ ruleQUICK_PROVE_HYP th #<< 
                               primINST [(tmM, dtm), (tmN, mtm), (tmP, ntm)] pth
               else do pth <- convNUM_LE_qth
                       tmM <- serve tmM'
                       tmN <- serve tmN'
                       tmP <- serve tmP'
                       dtm <- sbcbn mtm ntm
                       th <- ruleNUM_ADC dtm ntm
                       liftO $ ruleQUICK_PROVE_HYP th #<< 
                               primINST [(tmM, dtm), (tmN, mtm), (tmP, ntm)] pth
      _ -> fail "convNUM_LE"
  where convNUM_LE_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_pth = cacheProof "convNUM_LE_pth" ctxtWF $
            ruleUNDISCH =<< 
              prove "m + n = p ==> ((NUMERAL n <= NUMERAL p) <=> T)"
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [defNUMERAL] `_THEN`
                 tacMESON [thmLE_ADD, thmADD_SYM])

        convNUM_LE_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_qth = cacheProof "convNUM_LE_qth" ctxtWF $
            ruleUNDISCH =<< 
              prove "SUC(m + p) = n ==> (NUMERAL n <= NUMERAL p <=> F)"
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, thmNOT_LE
                            , thmADD_CLAUSES, thmLT_EXISTS ] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_LE_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_rth = cacheProof "convNUM_LE_rth" ctxtWF $
            prove "NUMERAL n <= NUMERAL n <=> T" $
              tacREWRITE [thmLE_REFL]

convNUM_EQ :: WFCtxt thry => Conversion cls thry
convNUM_EQ = Conv $ \ tm ->
    do tmM <- serve tmM'
       tmN <- serve tmN'
       tmP <- serve tmP'
       pth <- convNUM_EQ_pth
       qth <- convNUM_EQ_qth
       rth <- convNUM_EQ_rth
       case tm of
         (NUMERAL mtm := NUMERAL ntm) ->
             let rel = orderrelation mtm ntm in
               if rel == Just EQ 
               then liftO $ primINST [(tmN, ntm)] rth
               else if rel == Just LT 
                    then do dtm <- sbcbn ntm mtm
                            th <- ruleNUM_ADC dtm mtm
                            liftO $ ruleQUICK_PROVE_HYP th #<< 
                                      primINST [ (tmM, dtm), (tmN, mtm)
                                               , (tmP, ntm) ] pth
                    else do dtm <- sbcbn mtm ntm
                            th <- ruleNUM_ADC dtm ntm
                            liftO $ ruleQUICK_PROVE_HYP th #<< 
                                      primINST [ (tmM, dtm), (tmN, mtm)
                                               , (tmP, ntm) ] qth
         _ -> fail "convNUM_EQ"
  where convNUM_EQ_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_pth = cacheProof "convNUM_EQ_pth" ctxtWF $
            ruleUNDISCH =<< 
              prove "SUC(m + n) = p ==> ((NUMERAL n = NUMERAL p) <=> F)"
                (_DISCH_THEN (tacSUBST1 <#< ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, ruleGSYM thmLE_ANTISYM
                            , thmDE_MORGAN ] `_THEN`
                 tacREWRITE [thmNOT_LE, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_EQ_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_qth = cacheProof "convNUM_EQ_qth" ctxtWF $
            ruleUNDISCH =<< 
              prove "SUC(m + p) = n ==> ((NUMERAL n = NUMERAL p) <=> F)"
                (_DISCH_THEN (tacSUBST1 <#< ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, ruleGSYM thmLE_ANTISYM
                            , thmDE_MORGAN ] `_THEN`
                 tacREWRITE [thmNOT_LE, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_EQ_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_rth = cacheProof "convNUM_EQ_rth" ctxtWF $
            prove "(NUMERAL n = NUMERAL n) <=> T" tacREWRITE_NIL

convNUM_EXP :: WFCtxt thry =>Conversion cls thry
convNUM_EXP = Conv $ \ tm ->
    (do tth <- convNUM_EXP_tth
        th <- runConv (convGEN_REWRITE id [tth]) tm
        (lop, r) <- liftO $ destComb =<< rand (concl th)
        (_, l) <- liftO $ destComb lop
        if not (wellformed l && wellformed r)
           then fail ""
           else do th' <- ruleNUM_EXP_CONV l r
                   tm' <- liftO $ rand (concl th')
                   fth <- convNUM_EXP_fth
                   tmM <- serve tmM'
                   liftO $ liftM1 primTRANS (primTRANS th th') #<<
                             primINST [(tmM, tm')] fth) <?> "convNUM_EXP"
  where ruleNUM_EXP_CONV :: WFCtxt thry => HOLTerm -> HOLTerm
                         -> HOL cls thry HOLThm
        ruleNUM_EXP_CONV l (Const "_0" _) =
            do pth <- convNUM_EXP_pth
               tmM <- serve tmM'
               liftO $ primINST [(tmM, l)] pth
        ruleNUM_EXP_CONV l r =
            let (b, r') = fromJust $ destComb r in
              do tmBIT0 <- serve tmBIT0'
                 tmMul <- serve tmMul'
                 tmA <- serve tmA'
                 tmB <- serve tmB'
                 tmM <- serve tmM'
                 tmN <- serve tmN'
                 tmP <- serve tmP'
                 if b == tmBIT0
                    then do th1 <- ruleNUM_EXP_CONV l r'
                            let tm1 = fromJust . rand $ concl th1
                            th2 <- runConv convNUM_MULT' #<< 
                                     mkBinop tmMul tm1 tm1
                            let tm2 = fromJust . rand $ concl th2
                            pth <- convNUM_EXP_pth0
                            let th3 = fromJust $ 
                                      primINST [ (tmM, l), (tmN, r'), (tmP, tm1)
                                               , (tmB, tm2), (tmA, tm2) ] pth
                            ruleMP (ruleMP th3 th1) th2
                    else do th1 <- ruleNUM_EXP_CONV l r'
                            let tm1 = fromJust . rand $ concl th1
                            th2 <- runConv convNUM_MULT' #<<
                                     mkBinop tmMul tm1 tm1
                            let tm2 = fromJust . rand $ concl th2
                            th3 <- runConv convNUM_MULT' #<<
                                     mkBinop tmMul l tm2
                            let tm3 = fromJust . rand $ concl th3
                            pth <- convNUM_EXP_pth1
                            let th4 = fromJust $
                                      primINST [ (tmM, l), (tmN, r'), (tmP, tm1)
                                               , (tmB, tm2), (tmA, tm3) ] pth
                            ruleMP (ruleMP (ruleMP th4 th1) th2) th3
        convNUM_MULT' :: WFCtxt thry => Conversion cls thry
        convNUM_MULT' = Conv $ \ tm ->
            case tm of
              (Comb (Comb (Const "*" _) mtm) ntm)
                  | mtm == ntm ->
                      do th1 <- ruleNUM_SQUARE mtm
                         let ptm = fromJust . rand $ concl th1
                         pth <- convNUM_EXP_pth_refl
                         tmM <- serve tmM'
                         tmP <- serve tmP'
                         liftO $ primEQ_MP
                          (fromJust $ primINST [(tmM, mtm), (tmP, ptm)] pth) th1
                  | otherwise ->
                      let (w1, z1) = fromJust $ bitcounts mtm
                          (w2, z2) = fromJust $ bitcounts ntm in
                        ruleNUM_MUL (w1+z1) (w2+z2) mtm ntm
              _ -> fail "convNUM_MULT'" 

        convNUM_EXP_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth0 = cacheProof "convNUM_EXP_pth0" ctxtWF .
            prove "(m EXP n = p) ==> (p * p = a) ==> (m EXP (BIT0 n) = a)" $
              _REPEAT (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
              tacREWRITE [thmBIT0, thmEXP_ADD]

        convNUM_EXP_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth1 = cacheProof "convNUM_EXP_pth1" ctxtWF .
            prove [str| (m EXP n = p) ==> (p * p = b) ==> (m * b = a) 
                        ==> (m EXP (BIT1 n) = a) |] $
              _REPEAT (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
              tacREWRITE [thmBIT1, thmEXP_ADD, defEXP]

        convNUM_EXP_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth = cacheProof "convNUM_EXP_pth" ctxtWF .
            prove "m EXP _0 = BIT1 _0" $
              tacMP (ruleCONJUNCT1 defEXP) `_THEN` 
              tacREWRITE [defNUMERAL, thmBIT1] `_THEN`
              _DISCH_THEN tacMATCH_ACCEPT

        convNUM_EXP_tth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_tth = cacheProof "convNUM_EXP_tth" ctxtWF .
            prove "(NUMERAL m) EXP (NUMERAL n) = m EXP n" $
              tacREWRITE [defNUMERAL]

        convNUM_EXP_fth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_fth = cacheProof "convNUM_EXP_fth" ctxtWF .
            prove "m = NUMERAL m" $
              tacREWRITE [defNUMERAL]

        convNUM_EXP_pth_refl :: WFCtxt thry 
                             => HOL cls thry HOLThm
        convNUM_EXP_pth_refl = cacheProof "convNUM_EXP_pth_refl" ctxtWF $
            ruleMESON [thmEXP_2] "m EXP 2 = p <=> m * m = p"

convNUM_LT :: WFCtxt thry => Conversion cls thry
convNUM_LT = Conv $ \ tm ->
    case tm of
      (Comb (Comb (Const "<" _) (NUMERAL mtm)) (NUMERAL ntm)) ->
          let rel = fromJust $ orderrelation mtm ntm in
            if rel == EQ
            then do pth <- convNUM_LT_rth
                    tmN <- serve tmN'
                    liftO $ primINST [(tmN, ntm)] pth
            else if rel == LT
                 then do dtm <- sbcbn ntm mtm
                         th <- ruleNUM_ADC dtm mtm
                         pth <- convNUM_LT_pth
                         tmM <- serve tmM'
                         tmN <- serve tmN'
                         tmP <- serve tmP'
                         liftO $ ruleQUICK_PROVE_HYP th #<<
                           primINST [(tmM, dtm), (tmN, mtm), (tmP, ntm)] pth
                 else do dtm <- subbn mtm ntm
                         th <- ruleNUM_ADD dtm ntm
                         pth <- convNUM_LT_qth
                         tmM <- serve tmM'
                         tmN <- serve tmN'
                         tmP <- serve tmP'   
                         liftO $ ruleQUICK_PROVE_HYP th #<<
                           primINST [(tmM, dtm), (tmN, mtm), (tmP, ntm)] pth
      _ -> fail "convNUM_LT"
  where convNUM_LT_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_pth = cacheProof "convNUM_LT_pth" ctxtWF $
            ruleUNDISCH =<< 
              prove "SUC(m + n) = p ==> ((NUMERAL n < NUMERAL p) <=> T)"
                (tacREWRITE [defNUMERAL, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_LT_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_qth = cacheProof "convNUM_LT_qth" ctxtWF $
            ruleUNDISCH =<< 
              prove "m + p = n ==> (NUMERAL n < NUMERAL p <=> F)"
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [thmNOT_LT, defNUMERAL] `_THEN`
                 tacMESON [thmLE_ADD, thmADD_SYM])

        convNUM_LT_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_rth = cacheProof "convNUM_LT_rth" ctxtWF $
            prove "NUMERAL n < NUMERAL n <=> F" $ tacMESON[thmLT_REFL]
                           
ruleNUM_ADD :: WFCtxt thry => HOLTerm -> HOLTerm 
            -> HOL cls thry HOLThm
ruleNUM_ADD mtm ntm =
    let (mLo, mHi) = fromJust $ topsplit mtm
        (nLo, nHi) = fromJust $ topsplit ntm
        mInd = case mHi of
                 (Const "_0" _) -> mLo
                 _ -> mLo + 16
        nInd = case nHi of
                 (Const "_0" _) -> nLo
                 _ -> nLo + 16
        ind = 32 * mInd + nInd in
      do clauses <- addClauses
         let th1 = clauses V.! ind
         flags <- addFlags
         case flags V.! ind of
           0 -> do tmM <- serve tmM'
                   liftO $ primINST [(tmM, mHi)] th1
           1 -> do tmN <- serve tmN'
                   liftO $ primINST [(tmN, nHi)] th1
           2 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADD mHi nHi
                   tmM <- serve tmM'
                   tmN <- serve tmN'
                   tmP <- serve tmP'
                   let th3 = fromJust $ primINST [ (tmM, mHi), (tmN, nHi)
                                                 , (tmP, ptm)] th1
                   liftO $ primEQ_MP th3 th2
           3 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADC mHi nHi
                   tmM <- serve tmM'
                   tmN <- serve tmN'
                   tmP <- serve tmP'
                   let th3 = fromJust $ primINST [ (tmM, mHi), (tmN, nHi)
                                                 , (tmP, ptm)] th1
                   liftO $ primEQ_MP th3 th2
           _ -> fail "ruleNUM_ADD"

ruleNUM_ADC :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLThm
ruleNUM_ADC mtm ntm =
    let (mLo, mHi) = fromJust $ topsplit mtm
        (nLo, nHi) = fromJust $ topsplit ntm
        mInd = case mHi of
                 (Const "_0" _) -> mLo
                 _ -> mLo + 16
        nInd = case nHi of
                 (Const "_0" _) -> nLo
                 _ -> nLo + 16
        ind = 32 * mInd + nInd in
      do clauses <- adcClauses
         flags <- adcFlags
         let th1 = clauses V.! ind
         case flags V.! ind of
           0 -> do tmM <- serve tmM'
                   liftO $ primINST [(tmM, mHi)] th1
           1 -> do tmN <- serve tmN'
                   liftO $ primINST [(tmN, nHi)] th1
           2 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADD mHi nHi
                   tmM <- serve tmM'
                   tmN <- serve tmN'
                   tmP <- serve tmP'
                   let th3 = fromJust $ primINST [ (tmM, mHi), (tmN, nHi)
                                                 , (tmP, ptm)] th1
                   liftO $ primEQ_MP th3 th2
           3 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADC mHi nHi
                   tmM <- serve tmM'
                   tmN <- serve tmN'
                   tmP <- serve tmP'
                   let th3 = fromJust $ primINST [ (tmM, mHi), (tmN, nHi)
                                                 , (tmP, ptm)] th1
                   liftO $ primEQ_MP th3 th2
           _ -> fail "ruleNUM_ADC"


ruleNUM_MUL_pth_0 :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_0 = 
    cacheProofs ["ruleNUM_MUL_pth_0l", "ruleNUM_MUL_pth_0r"] ctxtWF $
      do th <- prove [str| _0 * n = _0 /\ m * _0 = _0 |] $
                 tacMESON [defNUMERAL, thmMULT_CLAUSES]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]

ruleNUM_MUL_pth_1 :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_1 = 
    cacheProofs ["ruleNUM_MUL_pth_1l", "ruleNUM_MUL_pth_1r"] ctxtWF $
      do th <- prove [str| (BIT1 _0) * n = n /\ m * (BIT1 _0) = m |] $
                 tacMESON [defNUMERAL, thmMULT_CLAUSES]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]
    
ruleNUM_MUL_pth_even :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_even = 
    cacheProofs ["ruleNUM_MUL_pth_evenl", "ruleNUM_MUL_pth_evenr"] ctxtWF $
      do th <- prove [str| (m * n = p <=> (BIT0 m) * n = BIT0 p) /\
                           (m * n = p <=> m * BIT0 n = BIT0 p) |] $
                 tacREWRITE [thmBIT0] `_THEN` 
                 tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                               "m * 2 * n = 2 * m * n"] `_THEN`
                 tacREWRITE [ ruleGSYM thmMULT_ASSOC
                            , thmEQ_MULT_LCANCEL, thmARITH_EQ ]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]


ruleNUM_MUL :: WFCtxt thry => Int -> Int -> HOLTerm 
            -> HOLTerm -> HOL cls thry HOLThm
ruleNUM_MUL _ _ (Const "_0" _) tm' =
    do pth <- ruleNUM_MUL_pth_0l
       tmN <- serve tmN'
       liftO $ primINST [(tmN, tm')] pth
  where ruleNUM_MUL_pth_0l :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_0l = ruleNUM_MUL_pth_0 !! 0
ruleNUM_MUL _ _ tm (Const "_0" _) =
    do pth <- ruleNUM_MUL_pth_0r
       tmM <- serve tmM'
       liftO $ primINST [(tmM, tm)] pth
  where ruleNUM_MUL_pth_0r :: WFCtxt thry => HOL cls thry HOLThm 
        ruleNUM_MUL_pth_0r = ruleNUM_MUL_pth_0 !! 1
ruleNUM_MUL _ _ (BIT1 (Const "_0" _)) tm' =
    do pth <- ruleNUM_MUL_pth_1l
       tmN <- serve tmN'
       liftO $ primINST [(tmN, tm')] pth
  where ruleNUM_MUL_pth_1l :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_1l = ruleNUM_MUL_pth_1 !! 0
ruleNUM_MUL _ _ tm (BIT1 (Const "_0" _)) =
    do pth <- ruleNUM_MUL_pth_1r
       tmM <- serve tmM'
       liftO $ primINST [(tmM, tm)] pth
  where ruleNUM_MUL_pth_1r :: WFCtxt thry => HOL cls thry HOLThm 
        ruleNUM_MUL_pth_1r = ruleNUM_MUL_pth_1 !! 1
ruleNUM_MUL k l (BIT0 mtm) tm' =
    do th0 <- ruleNUM_MUL (k - 1) l mtm tm'
       pth <- ruleNUM_MUL_pth_evenl
       tmM <- serve tmM'
       tmN <- serve tmN'
       tmP <- serve tmP'
       let tm0 = fromJust . rand $ concl th0
           th1 = fromJust $ primINST [(tmM, mtm), (tmN, tm'), (tmP, tm0)] pth
       liftO $ primEQ_MP th1 th0
  where ruleNUM_MUL_pth_evenl :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_evenl = ruleNUM_MUL_pth_even !! 0
ruleNUM_MUL k l tm (BIT0 ntm) =
    do th0 <- ruleNUM_MUL k (l - 1) tm ntm
       pth <- ruleNUM_MUL_pth_evenr
       tmM <- serve tmM'
       tmN <- serve tmN'
       tmP <- serve tmP'
       let tm0 = fromJust . rand $ concl th0
           th1 = fromJust $ primINST [(tmM, tm), (tmN, ntm), (tmP, tm0)] pth
       liftO $ primEQ_MP th1 th0
  where ruleNUM_MUL_pth_evenr :: WFCtxt thry => HOL cls thry HOLThm 
        ruleNUM_MUL_pth_evenr = ruleNUM_MUL_pth_even !! 1
ruleNUM_MUL k l tm@(BIT1 mtm) tm'@(BIT1 ntm)
    | k <= 50 || l <= 50 || k * k < l || l * l < k =
        case (mtm, ntm) of
          (BIT1 (BIT1 _), _) ->
              do pth <- ruleNUM_MUL_pth_recodel
                 tmA <- serve tmA'
                 tmM <- serve tmM'
                 tmN <- serve tmN'
                 tmP <- serve tmP'
                 tmZero <- serve tmZero'
                 th1 <- ruleNUM_ADC tmZero tm
                 let ptm = fromJust . rand $ concl th1
                 th2 <- ruleNUM_MUL k l ptm tm'
                 let tm2 = fromJust . rand $ concl th2
                 atm <- subbn tm2 tm'
                 let th3 = fromJust $ primINST [ (tmM, tm), (tmN, tm')
                                               , (tmP, ptm), (tmA, atm) ] pth
                     th4 = rulePROVE_HYP th1 th3
                 th5 <- ruleNUM_ADD atm tm'
                 liftO $ primEQ_MP th4 =<< primTRANS th2 =<< ruleSYM th5
          (_, BIT1 (BIT1 _)) ->
              do pth <- ruleNUM_MUL_pth_recoder
                 tmA <- serve tmA'
                 tmM <- serve tmM'
                 tmN <- serve tmN'
                 tmP <- serve tmP'
                 tmZero <- serve tmZero'
                 th1 <- ruleNUM_ADC tmZero tm'
                 let ptm = fromJust . rand $ concl th1
                 th2 <- ruleNUM_MUL k l tm ptm
                 let tm2 = fromJust . rand $ concl th2
                 atm <- subbn tm2 tm
                 let th3 = fromJust $ primINST [ (tmM, tm), (tmN, tm')
                                               , (tmP, ptm), (tmA, atm) ] pth
                     th4 = rulePROVE_HYP th1 th3
                 th5 <- ruleNUM_ADD atm tm
                 liftO $ primEQ_MP th4 =<< primTRANS th2 =<< ruleSYM th5
          _
            |  k <= l -> 
                do pth <- ruleNUM_MUL_pth_oddl
                   tmM <- serve tmM'
                   tmN <- serve tmN'
                   tmP <- serve tmP'
                   th0 <- ruleNUM_MUL (k - 1) l mtm tm'
                   let ptm = fromJust . rand $ concl th0 
                       th1 = fromRight $ primEQ_MP 
                               (fromJust $ primINST [ (tmM, mtm), (tmN, tm')
                                                    , (tmP, ptm)] pth) th0
                       tm1 = fromJust $ lHand =<< rand (concl th1)
                   th2 <- ruleNUM_ADD tm1 tm'
                   liftO $ primTRANS th1 th2
              | otherwise ->
                  do pth <- ruleNUM_MUL_pth_oddr
                     tmM <- serve tmM'
                     tmN <- serve tmN'
                     tmP <- serve tmP'
                     th0 <- ruleNUM_MUL k (l - 1) tm ntm
                     let ptm = fromJust . rand $ concl th0
                         th1 = fromRight $ primEQ_MP
                                 (fromJust $ primINST [ (tmM, tm), (tmN, ntm)
                                                      , (tmP, ptm) ] pth) th0
                         tm1 = fromJust $ lHand =<< rand (concl th1)
                     th2 <- ruleNUM_ADD tm1 tm
                     liftO $ primTRANS th1 th2
    | otherwise =
        let mval = fromJust $ destRawNumeral mtm
            nval = fromJust $ destRawNumeral ntm in
          if nval <= mval
             then do pth <- ruleNUM_MUL_pth_oo1
                     tmA <- serve tmA'
                     tmB <- serve tmB'
                     tmC <- serve tmC'
                     tmD <- serve tmD'
                     tmM <- serve tmM'
                     tmN <- serve tmN'
                     tmP <- serve tmP'
                     n <- mkNumeral (mval - nval)
                     let ptm = fromJust $ rand n
                     th2 <- ruleNUM_ADD ntm ptm
                     th3 <- ruleNUM_ADC mtm ntm
                     let atm = fromJust . rand $ concl th3
                     th4 <- ruleNUM_SQUARE ptm
                     let btm = fromJust . rand $ concl th4
                     th5 <- ruleNUM_SQUARE atm
                     let ctm = fromJust . rand $ concl th5
                     dtm <- subbn ctm btm
                     th6 <- ruleNUM_ADD btm dtm
                     let th1 = fromJust $ primINST [ (tmA, atm), (tmB, btm)
                                                   , (tmC, ctm), (tmD, dtm)
                                                   , (tmM, mtm), (tmN, ntm)
                                                   , (tmP, ptm) ] pth
                     th7 <- foldr1M ruleCONJ [th2, th3, th4, th5, th6]
                     liftO $ ruleQUICK_PROVE_HYP th7 th1
             else do pth <-  ruleNUM_MUL_pth_oo2
                     tmA <- serve tmA'
                     tmB <- serve tmB'
                     tmC <- serve tmC'
                     tmD <- serve tmD'
                     tmM <- serve tmM'
                     tmN <- serve tmN'
                     tmP <- serve tmP'
                     n <- mkNumeral (nval - mval)
                     let ptm = fromJust $ rand n
                     th2 <- ruleNUM_ADD mtm ptm
                     th3 <- ruleNUM_ADC ntm mtm
                     let atm = fromJust . rand $ concl th3
                     th4 <- ruleNUM_SQUARE ptm
                     let btm = fromJust . rand $ concl th4
                     th5 <- ruleNUM_SQUARE atm
                     let ctm = fromJust . rand $ concl th5
                     dtm <- subbn ctm btm
                     th6 <- ruleNUM_ADD btm dtm
                     let th1 = fromJust $ primINST [ (tmA, atm), (tmB, btm)
                                                   , (tmC, ctm), (tmD, dtm)
                                                   , (tmM, mtm), (tmN, ntm)
                                                   , (tmP, ptm) ] pth
                     th7 <- foldr1M ruleCONJ [th2, th3, th4, th5, th6]
                     liftO $ ruleQUICK_PROVE_HYP th7 th1
  where ruleNUM_MUL_pth_oo :: WFCtxt thry => [HOL cls thry HOLThm]
        ruleNUM_MUL_pth_oo = 
            cacheProofs ["ruleNUM_MUL_pth_oo1", "ruleNUM_MUL_pth_oo2"] ctxtWF $
                do tmM <- serve tmM'
                   tmN <- serve tmN'
                   th1 <- prove [str| n + p = m /\ SUC(m + n) = a /\ 
                                      p EXP 2 = b /\ a EXP 2 = c /\ b + d = c
                                      ==> ((BIT1 m) * (BIT1 n) = d) |] $ 
                            tacABBREV "two = 2" `_THEN` 
                            tacREWRITE [thmBIT1, thmIMP_CONJ] `_THEN`
                            _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
                            tacREWRITE [thmEXP_2, ruleGSYM thmMULT_2] `_THEN`
                            tacREPLICATE 4 (_DISCH_THEN 
                                            (tacSUBST1 . ruleSYM)) `_THEN`
                            tacREWRITE [thmADD1, runConv (convAC thmADD_AC) =<< 
                                       toHTm [str| ((n + p) + n) + 1 = 
                                                   (p + (n + n)) + 1 |]] `_THEN`
                            tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                            tacREWRITE [ thmLEFT_ADD_DISTRIB
                                       , thmRIGHT_ADD_DISTRIB ] `_THEN`
                            tacREWRITE [ ruleGSYM thmADD_ASSOC, thmMULT_CLAUSES
                                       , thmEQ_ADD_LCANCEL ] `_THEN`
                            _DISCH_THEN tacSUBST1 `_THEN`
                            tacREWRITE [ thmMULT_2, thmLEFT_ADD_DISTRIB
                                       , thmRIGHT_ADD_DISTRIB ] `_THEN`
                            tacREWRITE [thmMULT_AC] `_THEN` 
                            tacREWRITE [thmADD_AC]
                   th2 <- ruleUNDISCH_ALL th1
                   let th3 = fromJust $ primINST [(tmM, tmN), (tmN, tmM)] th2
                   th4 <- rulePURE_ONCE_REWRITE [thmMULT_SYM] th3
                   return [th2, th4]
        ruleNUM_MUL_pth_oo1 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_oo1 = ruleNUM_MUL_pth_oo !! 0
        ruleNUM_MUL_pth_oo2 :: WFCtxt thry => HOL cls thry HOLThm 
        ruleNUM_MUL_pth_oo2 = ruleNUM_MUL_pth_oo !! 1

        ruleNUM_MUL_pth_odd :: WFCtxt thry => [HOL cls thry HOLThm]
        ruleNUM_MUL_pth_odd = 
            cacheProofs ["ruleNUM_MUL_pth_oddl", "ruleNUM_MUL_pth_oddr"] ctxtWF $
                do th <- prove [str|(m * n = p <=> BIT1 m * n = BIT0 p + n) /\
                                    (m * n = p <=> m * BIT1 n = BIT0 p + m) |] $
                           tacREWRITE [thmBIT0, thmBIT1] `_THEN` 
                           tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                           tacREWRITE [thmMULT_CLAUSES] `_THEN`
                           tacREWRITE [ruleMESON [thmMULT_AC, thmADD_SYM]
                                        "m + m * 2 * n = 2 * m * n + m"] `_THEN`
                           tacREWRITE [ ruleGSYM thmMULT_ASSOC
                                      , thmEQ_MULT_LCANCEL
                                      , thmEQ_ADD_RCANCEL ] `_THEN`
                           tacREWRITE [thmARITH_EQ]
                   (th1, th2) <- ruleCONJ_PAIR th
                   return [th1, th2]
        ruleNUM_MUL_pth_oddl :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_oddl = ruleNUM_MUL_pth_odd !! 0
        ruleNUM_MUL_pth_oddr :: WFCtxt thry => HOL cls thry HOLThm 
        ruleNUM_MUL_pth_oddr = ruleNUM_MUL_pth_odd !! 1

        ruleNUM_MUL_pth_recodel :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_recodel = cacheProof "ruleNUM_MUL_pth_recodel" ctxtWF $
            do th <- prove "SUC(_0 + m) = p ==> (p * n = a + n <=> m * n = a)" $
                       tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
                       _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                       tacREWRITE [thmADD_CLAUSES, thmMULT_CLAUSES
                                  , thmEQ_ADD_RCANCEL]
               ruleUNDISCH_ALL th

        ruleNUM_MUL_pth_recoder :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_recoder = cacheProof "ruleNUM_MUL_pth_recoder" ctxtWF $
            do th <- prove "SUC(_0 + n) = p ==> (m * p = a + m <=> m * n = a)" $
                       tacONCE_REWRITE [thmMULT_SYM] `_THEN`
                       tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
                       _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                       tacREWRITE [thmADD_CLAUSES, thmMULT_CLAUSES
                                  , thmEQ_ADD_RCANCEL]
               ruleUNDISCH_ALL th
ruleNUM_MUL _ _ _ _ = fail "ruleNUM_MUL"
              
convNUM_SHIFT :: WFCtxt thry => Int -> Conversion cls thry
convNUM_SHIFT k = Conv $ \ tm ->
    if k <= 0
    then do pth <- convNUM_SHIFT_pth_base
            tmN <- serve tmN'
            liftO $ primINST [(tmN, tm)] pth
    else case tm of 
           (Comb _ (Comb _ (Comb _ (Comb _ _))))
               | k >= 4 ->
                   let (i, ntm) = fromJust $ topsplit tm in
                     do th1 <- runConv (convNUM_SHIFT (k - 4)) ntm
                        case concl th1 of
                          (Comb _ (Comb (Comb _ (Const "_0" _)) 
                                   (Comb (Comb _ ptm) btm))) ->
                            do tmB <- serve tmB'
                               tmN <- serve tmN'
                               tmP <- serve tmP'
                               pths <- convNUM_SHIFT_pths0
                               let th2 = pths V.! i
                               let th3 = fromJust $ 
                                           primINST [ (tmN, ntm), (tmB, btm)
                                                    , (tmP, ptm) ]  th2
                               liftO $ primEQ_MP th3 th1
                          (Comb _ (Comb (Comb _ atm) 
                                   (Comb (Comb _ ptm) btm))) ->
                            do tmA <- serve tmA'
                               tmB <- serve tmB'
                               tmN <- serve tmN'
                               tmP <- serve tmP'
                               pths <- convNUM_SHIFT_pths1
                               let th2 = pths V.! i
                               let th3 = fromJust $
                                           primINST [ (tmN, ntm), (tmA, atm)
                                                    , (tmB, btm), (tmP, ptm)
                                                    ] th2
                               liftO $ primEQ_MP th3 th1
                          _ -> fail "convNUM_SHIFT"
               | otherwise -> fail "convNUM_SHIFT: malformed numeral"
           (BIT0 ntm) ->
               do th1 <- runConv (convNUM_SHIFT (k - 1)) ntm
                  case concl th1 of
                    (Comb _ (Comb (Comb _ (Const "_0" _))
                             (Comb (Comb _ ptm) btm))) ->
                      do pth <- convNUM_SHIFT_pthz
                         tmB <- serve tmB'
                         tmN <- serve tmN'
                         tmP <- serve tmP'
                         liftO $ primEQ_MP
                           (fromJust $ primINST [ (tmN, ntm), (tmB, btm)
                                                , (tmP, ptm) ] pth) th1
                    (Comb _ (Comb (Comb _ atm)
                             (Comb (Comb _ ptm) btm))) ->
                      do pth <- convNUM_SHIFT_pth0
                         tmA <- serve tmA'
                         tmB <- serve tmB'
                         tmN <- serve tmN'
                         tmP <- serve tmP'
                         liftO $ primEQ_MP
                           (fromJust $ primINST [ (tmN, ntm), (tmA, atm)
                                                , (tmB, btm), (tmP, ptm) 
                                                ] pth) th1 
                    _ -> fail "convNUM_SHIFT"
           (BIT1 ntm) ->
               do th1 <- runConv (convNUM_SHIFT (k - 1)) ntm
                  let (Comb _ (Comb (Comb _ atm)
                               (Comb (Comb _ ptm) btm))) = concl th1
                  pth <- convNUM_SHIFT_pth1
                  tmA <- serve tmA'
                  tmB <- serve tmB'
                  tmN <- serve tmN'
                  tmP <- serve tmP'
                  liftO $ primEQ_MP
                    (fromJust $ primINST [ (tmN, ntm), (tmA, atm)
                                         , (tmB, btm), (tmP, ptm) ] pth) th1 
           (Const "_0" _) ->
               do th1 <- runConv (convNUM_SHIFT (k - 1)) tm
                  let (Comb _ (Comb (Comb _ atm)
                               (Comb (Comb _ ptm) btm))) = concl th1
                  pth <- convNUM_SHIFT_pth_triv
                  tmA <- serve tmA'
                  tmB <- serve tmB'
                  tmP <- serve tmP'
                  liftO $ primEQ_MP
                    (fromJust $ primINST [ (tmA, atm), (tmB, btm)
                                         , (tmP, ptm) ] pth) th1 
           _ -> fail "convNUM_SHIFT: malformed numeral"
  where convNUM_SHIFT_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth0 = cacheProof "convNUM_SHIFT_pth0" ctxtWF .
            prove "(n = a + p * b <=> BIT0 n = BIT0 a + BIT0 p * b)" $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_SHIFT_pthz :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pthz = cacheProof "convNUM_SHIFT_pthz" ctxtWF $
            do th1 <- ruleSPEC "_0" defNUMERAL
               prove "n = _0 + p * b <=> BIT0 n = _0 + BIT0 p * b" $
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN`
                 tacREWRITE [thmADD_CLAUSES, ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [ ruleGSYM thmMULT_ASSOC, thmEQ_MULT_LCANCEL
                            , thmARITH_EQ ]

        convNUM_SHIFT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth1 = cacheProof "convNUM_SHIFT_pth1" ctxtWF .
            prove "(n = a + p * b <=> BIT1 n = BIT1 a + BIT0 p * b)" $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB, thmADD_CLAUSES
                         , thmSUC_INJ ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_SHIFT_pth_base :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth_base = cacheProof "convNUM_SHIFT_pth_base" ctxtWF .
            prove "n = _0 + BIT1 _0 * n" $
              tacMESON [thmADD_CLAUSES, thmMULT_CLAUSES, defNUMERAL]

        convNUM_SHIFT_pth_triv :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth_triv = cacheProof "convNUM_SHIFT_pth_triv" ctxtWF $
            do th1 <- ruleSPEC "_0" defNUMERAL
               prove "_0 = a + p * b <=> _0 = a + BIT0 p * b" $
                 tacCONV (convBINOP convSYM) `_THEN`
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmADD_EQ_0, thmMULT_EQ_0, thmBIT0]
                      
convNUM_UNSHIFT :: WFCtxt thry => Conversion cls thry
convNUM_UNSHIFT = Conv $ \ tm ->
    case tm of
      (Comb (Comb (Const "+" _) atm) (Comb (Comb (Const "*" _) ptm) btm)) ->
          case (atm, ptm, btm) of
            (_, _, Const "_0" _) ->
                do pth <- convNUM_UNSHIFT_pth_triv
                   tmA <- serve tmA'
                   tmP <- serve tmP'
                   liftO $ primINST [(tmA, atm), (tmP, ptm)] pth
            (_, BIT1 (Const "_0" _), _) ->
                do pth <- convNUM_UNSHIFT_pth_base
                   tmA <- serve tmA'
                   tmB <- serve tmB'
                   let th1 = fromJust $ primINST [(tmA, atm), (tmB, btm)] pth
                       (Comb _ (Comb (Comb _ mtm) ntm)) = concl th1
                   th2 <- ruleNUM_ADD mtm ntm
                   liftO $ primTRANS th1 th2
            (Comb _ (Comb _ (Comb _ (Comb _ atm'))),
             Comb _ (Comb _ (Comb _ (Comb _ ptm'@(Comb _ _)))), _) ->
                let (i, _) = fromJust $ topsplit atm in
                  case (atm', ptm') of
                    (Comb _ (Comb _ (Comb _ (Comb _ atm''))),
                     Comb _ (Comb _ (Comb _ (Comb _ ptm''@(Comb _ _))))) ->
                        do tmAdd <- serve tmAdd'
                           tmMul <- serve tmMul'
                           let (j, _) = fromJust $ topsplit atm'
                               tm' = fromRight $ liftM1 mkComb
                                       (mkComb tmAdd atm'') =<<
                                         liftM1 mkComb (mkComb tmMul ptm'') btm
                           th1 <- runConv convNUM_UNSHIFT tm'
                           tmA <- serve tmA'
                           tmB <- serve tmB'
                           tmN <- serve tmN'
                           tmP <- serve tmP'
                           pths <- convNUM_UNSHIFT_puths2
                           let pth = pths V.! (16 * j + i)
                               ntm = fromJust . rand $ concl th1
                               th2 = fromJust $ 
                                       primINST [ (tmA, atm''), (tmP, ptm'')
                                                , (tmB, btm), (tmN, ntm) ] pth
                           liftO $ primEQ_MP th2 th1
                    _ -> 
                        do tmAdd <- serve tmAdd'
                           tmMul <- serve tmMul'
                           let tm' = fromRight $ liftM1 mkComb
                                       (mkComb tmAdd atm') =<<
                                         liftM1 mkComb (mkComb tmMul ptm') btm
                           th1 <- runConv convNUM_UNSHIFT tm'
                           tmA <- serve tmA'
                           tmB <- serve tmB'
                           tmN <- serve tmN'
                           tmP <- serve tmP'
                           pths <- convNUM_UNSHIFT_puths1
                           let pth = pths V.! i
                               ntm = fromJust . rand $ concl th1
                               th2 = fromJust $
                                       primINST [ (tmA, atm'), (tmP, ptm')
                                                , (tmB, btm), (tmN, ntm) ] pth
                           liftO $ primEQ_MP th2 th1
            (Const "_0" _, BIT0 qtm, _) ->
                do pth <- convNUM_UNSHIFT_pthz
                   tmB <- serve tmB'
                   tmP <- serve tmP'
                   let th1 = fromJust $ primINST [(tmB, btm), (tmP, qtm)] pth
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            (BIT0 ctm, BIT0 qtm, _) ->
                do pth <- convNUM_UNSHIFT_pth0
                   tmA <- serve tmA'
                   tmB <- serve tmB'
                   tmP <- serve tmP'
                   let th1 = fromJust $ primINST [ (tmA, ctm), (tmB, btm)
                                                 , (tmP, qtm) ] pth
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            (BIT1 ctm, BIT0 qtm, _) ->
                do pth <- convNUM_UNSHIFT_pth1
                   tmA <- serve tmA'
                   tmB <- serve tmB'
                   tmP <- serve tmP'
                   let th1 = fromJust $ primINST [ (tmA, ctm), (tmB, btm)
                                                 , (tmP, qtm) ] pth
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            _ -> fail "convNUM_UNSHIFT: malformed numeral"
      _ -> fail "convNUM_UNSHIFT: malformed numeral"
  where convNUM_UNSHIFT_pth_triv :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth_triv = cacheProof "convNUM_UNSHIFT_pth_triv" ctxtWF $
            do th1 <- ruleSPEC "_0" defNUMERAL
               prove "a + p * _0 = a" $
                 tacSUBST1 (ruleSYM th1) `_THEN` 
                 tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES]

        convNUM_UNSHIFT_pth_base :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth_base = cacheProof "convNUM_UNSHIFT_pth_base" ctxtWF $
            do th1 <- ruleSPEC "BIT1 _0" defNUMERAL
               prove "a + BIT1 _0 * b = a + b" $
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES]

        convNUM_UNSHIFT_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth0 = cacheProof "convNUM_UNSHIFT_pth0" ctxtWF .
            prove "BIT0 a + BIT0 p * b = BIT0(a + p * b)" $
              tacREWRITE [thmBIT0] `_THEN` tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [ruleGSYM thmMULT_ASSOC, ruleGSYM thmLEFT_ADD_DISTRIB]

        convNUM_UNSHIFT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth1 = cacheProof "convNUM_UNSHIFT_pth1" ctxtWF .
            prove "BIT1 a + BIT0 p * b = BIT1(a + p * b)" $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [thmADD_CLAUSES, thmSUC_INJ] `_THEN`
              tacREWRITE [ruleGSYM thmMULT_ASSOC, ruleGSYM thmLEFT_ADD_DISTRIB] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_UNSHIFT_pthz :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pthz = cacheProof "convNUM_UNSHIFT_pthz" ctxtWF $
            do th1 <- ruleSPEC "_0" defNUMERAL
               prove "_0 + BIT0 p * b = BIT0(_0 + p * b)" $
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN` 
                 tacREWRITE [thmADD_CLAUSES] `_THEN`
                 tacREWRITE [thmRIGHT_ADD_DISTRIB]

ruleNUM_SQUARE :: WFCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleNUM_SQUARE tm =
    let (w, z) = fromJust $ bitcounts tm in
      ruleGEN_NUM_SQUARE w z tm
  where ruleGEN_NUM_SQUARE :: WFCtxt thry => Int -> Int 
                           -> HOLTerm -> HOL cls thry HOLThm
        ruleGEN_NUM_SQUARE _ _ (Const "_0" _) = 
            ruleNUM_SQUARE_pth0
        ruleGEN_NUM_SQUARE w z (BIT0 (BIT0 (BIT0 ptm))) =
            do th1 <- ruleGEN_NUM_SQUARE w (z - 3) ptm
               let ntm = fromJust . rand $ concl th1
               pth <- ruleNUM_SQUARE_pth_even3
               tmM <- serve tmM'
               tmN <- serve tmN'
               liftO $ 
                primEQ_MP (fromJust $ primINST [(tmM, ptm), (tmN, ntm)] pth) th1
        ruleGEN_NUM_SQUARE w z (BIT0 mtm) =
            do th1 <- ruleGEN_NUM_SQUARE w (z - 1) mtm
               let ntm = fromJust . rand $ concl th1
               pth <- ruleNUM_SQUARE_pth_even
               tmM <- serve tmM'
               tmN <- serve tmN'
               liftO $
                primEQ_MP (fromJust $ primINST [(tmM, mtm), (tmN, ntm)] pth) th1
        ruleGEN_NUM_SQUARE _ _ (BIT1 (Const "_0" _)) =
            ruleNUM_SQUARE_pth1
        ruleGEN_NUM_SQUARE w z (BIT1 mtm)
            | (w < 100 || z < 20) && w + z < 150 =
                case mtm of
                  (BIT1 (BIT1 ntm)) ->
                      do tmBIT0 <- serve tmBIT0'
                         tmOne <- serve [wF| BIT1 _0 |]
                         th1 <- ruleNUM_ADD ntm tmOne
                         let mtm' = fromJust . rand $ concl th1
                         th2 <- ruleNUM_SQUARE mtm'
                         let ptm = fromJust . rand $ concl th2
                         atm <- subbn (fromRight $ mkComb tmBIT0 =<< 
                                                     mkComb tmBIT0 ptm) mtm'
                         th3 <- ruleNUM_ADD mtm' atm
                         pth <- ruleNUM_SQUARE_pth_qstep
                         tmA <- serve tmA'
                         tmM <- serve tmM'
                         tmN <- serve tmN'
                         tmP <- serve tmP'
                         let th4 = fromJust $ 
                                     primINST [ (tmA, atm), (tmM, mtm')
                                              , (tmN, ntm), (tmP, ptm) ] pth
                         th5 <- ruleCONJ th1 =<< ruleCONJ th2 th3
                         liftO $ ruleQUICK_PROVE_HYP th5 th4
                  _ ->
                      do th1 <- ruleGEN_NUM_SQUARE (w - 1) z mtm
                         let ntm = fromJust . rand $ concl th1
                         pth <- ruleNUM_SQUARE_pth_odd
                         tmM <- serve tmM'
                         tmN <- serve tmN'
                         let th2 = fromRight $ primEQ_MP (fromJust $ 
                                                primINST [ (tmM, mtm)
                                                         , (tmN, ntm) ] pth) th1
                             (Comb _ (Comb _ (Comb _ 
                              (Comb (Comb _ ptm) qtm)))) = concl th2
                         th3 <- ruleNUM_ADD ptm qtm
                         th4 <- ruleAP_BIT1 =<< ruleAP_BIT0 th3
                         liftO $ primTRANS th2 th4
            | w + z < 800 =
               let k2 = (w + z) `div` 2 in
                 do th1 <- runConv (convNUM_SHIFT k2) tm
                    let (Comb (Comb _ ltm) 
                         (Comb (Comb _ ptm) htm)) = fromJust . rand $ concl th1
                    th2 <- ruleNUM_ADD htm ltm
                    let mtm' = fromJust . rand $ concl th2
                    th3 <- ruleNUM_SQUARE htm
                    th4 <- ruleNUM_SQUARE ltm
                    th5 <- ruleNUM_SQUARE mtm'
                    let atm = fromJust . rand $ concl th3
                        ctm = fromJust . rand $ concl th4
                        dtm = fromJust . rand $ concl th5
                    th6 <- ruleNUM_ADD atm ctm
                    let etm = fromJust . rand $ concl th6
                    btm <- subbn dtm etm
                    th7 <- ruleNUM_ADD etm btm
                    let dtm' = fromJust . rand $ concl th7
                    pth <- ruleNUM_SQUARE_pth_rec
                    tmA <- serve tmA'
                    tmB <- serve tmB'
                    tmC <- serve tmC'
                    tmD <- serve tmD'
                    tmE <- serve tmE'
                    tmH <- serve tmH'
                    tmL <- serve tmL'
                    tmM <- serve tmM'
                    tmN <- serve tmN'
                    tmP <- serve tmP'
                    let th8 = fromJust $ 
                                primINST [ (tmA, atm), (tmB, btm), (tmC, ctm)
                                         , (tmD, dtm'), (tmE, etm), (tmH, htm)
                                         , (tmL, tm), (tmM, mtm'), (tmN, tm)
                                         , (tmP, ptm)] pth
                    th9 <- foldr1M ruleCONJ [th1, th2, th3, th4, th5, th6, th7]
                    let th10 = fromRight $ ruleQUICK_PROVE_HYP th9 th8
                    ruleCONV (convRAND (convRAND 
                                        (convRAND convNUM_UNSHIFT) `_THEN` 
                                        convNUM_UNSHIFT)) th10
            | otherwise =
                let k3 = (w + z) `div` 3 in
                  do th0 <- runConv (convNUM_SHIFT k3 `_THEN`
                                     convRAND (convRAND (convNUM_SHIFT k3))) tm
                     let (Comb (Comb _ ltm) 
                          (Comb (Comb _ ptm)
                          (Comb (Comb _ mtm') 
                           (Comb (Comb _ _) htm)))) = fromJust . rand $ 
                                                        concl th0
                     th1 <- ruleNUM_SQUARE htm
                     th2 <- ruleNUM_SQUARE ltm
                     let atm = fromJust . rand $ concl th2
                         etm = fromJust . rand $ concl th1
                         lnum = fromJust $ destRawNumeral ltm
                         mnum = fromJust $ destRawNumeral mtm'
                         hnum = fromJust $ destRawNumeral htm
                     b <- mkNumeral $ 2 * lnum * mnum
                     let btm = fromJust $ rand b
                     c <- mkNumeral $ mnum * mnum + 2 * lnum * hnum
                     let ctm = fromJust $ rand c
                     d <- mkNumeral $ 2 * hnum * mnum
                     let dtm = fromJust $ rand d
                     pth <- ruleNUM_SQUARE_pth_toom3
                     tmA <- serve tmA'
                     tmB <- serve tmB'
                     tmC <- serve tmC'
                     tmD <- serve tmD'
                     tmE <- serve tmE'
                     tmH <- serve tmH'
                     tmL <- serve tmL'
                     tmM <- serve tmM'
                     tmP <- serve tmP'
                     let th = fromJust $ 
                                primINST [ (tmA, atm), (tmB, btm), (tmC, ctm)
                                         , (tmD, dtm), (tmE, etm), (tmH, htm)
                                         , (tmM, mtm'), (tmL, ltm)
                                         , (tmP, ptm) ] pth
                     th' <- ruleCONV (convBINOP2 (convRAND (convRAND 
                                      (convBINOP2 convTOOM3 
                                       (convBINOP2 convTOOM3 convTOOM3)))) 
                                      convTOOM3) th
                     let [tm3, tm4, tm5] = conjuncts . fromJust $ rand =<< 
                                             rand =<< lHand (concl th')
                     th3 <- ruleNUM_SQUARE #<< lHand =<< lHand tm3
                     th4 <- ruleNUM_SQUARE #<< lHand =<< lHand tm4
                     th5 <- ruleNUM_SQUARE #<< lHand =<< lHand tm5
                     ruleMP th' =<< foldr1M ruleCONJ [th1, th2, th3, th4, th5]
        ruleGEN_NUM_SQUARE _ _ _ = fail "ruleGEN_NUM_SQUARE"
       
        convTOOM3 :: WFCtxt thry => Conversion cls thry
        convTOOM3 = convBINOP2 (convLAND convNUM_UNSHIFT2) convNUM_UNSHIFT4

        convBINOP2 :: Conversion cls thry 
                   -> Conversion cls thry 
                   -> Conversion cls thry
        convBINOP2 conv1 = convCOMB2 (convRAND conv1)

        convNUM_UNSHIFT4 :: WFCtxt thry => Conversion cls thry
        convNUM_UNSHIFT4 = convRAND (convRAND convNUM_UNSHIFT3) `_THEN`
                           convNUM_UNSHIFT

        convNUM_UNSHIFT3 :: WFCtxt thry => Conversion cls thry
        convNUM_UNSHIFT3 = convRAND (convRAND convNUM_UNSHIFT2) `_THEN`
                           convNUM_UNSHIFT

        convNUM_UNSHIFT2 :: WFCtxt thry => Conversion cls thry
        convNUM_UNSHIFT2 = convRAND (convRAND convNUM_UNSHIFT) `_THEN`
                           convNUM_UNSHIFT

        ruleNUM_SQUARE_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth0 = cacheProof "ruleNUM_SQUARE_pth0" ctxtWF .
            prove "_0 EXP 2 = _0" $
              tacMESON [ defNUMERAL
                       , runConv (convREWRITE [thmARITH]) =<< toHTm "0 EXP 2" ]

        ruleNUM_SQUARE_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth1 = cacheProof "ruleNUM_SQUARE_pth1" ctxtWF .
            prove "(BIT1 _0) EXP 2 = BIT1 _0" $
              tacMESON [ defNUMERAL
                       , runConv (convREWRITE [thmARITH]) =<< toHTm "1 EXP 2" ]

        ruleNUM_SQUARE_pth_even :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_even = cacheProof "ruleNUM_SQUARE_pth_even" ctxtWF .
            prove "m EXP 2 = n <=> (BIT0 m) EXP 2 = BIT0(BIT0 n)" $
              tacABBREV "two = 2" `_THEN`
              tacREWRITE [thmBIT0] `_THEN` tacEXPAND "two" `_THEN`
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN` 
              tacREWRITE [thmEXP_2] `_THEN`
              tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                            "(2 * m) * (2 * n) = 2 * 2 * m * n"] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        ruleNUM_SQUARE_pth_odd :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_odd = cacheProof "ruleNUM_SQUARE_pth_odd" ctxtWF .
            prove "m EXP 2 = n <=> (BIT1 m) EXP 2 = BIT1(BIT0(m + n))" $
              tacABBREV "two = 2" `_THEN`
              tacREWRITE [defNUMERAL, thmBIT0, thmBIT1] `_THEN`
              tacEXPAND "two" `_THEN` tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [thmEXP_2, thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
              tacREWRITE [ thmSUC_INJ, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [runConv (convAC thmADD_AC) =<< toHTm
                            "(m + m * 2 * m) + m = m * 2 * m + m + m"] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2
                         , runConv (convAC thmMULT_AC) =<< toHTm
                             "m * 2 * m = 2 * m * m"] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ] `_THEN`
              tacGEN_REWRITE (convRAND . convRAND) [thmADD_SYM] `_THEN`
              tacREWRITE [thmEQ_ADD_RCANCEL]

        ruleNUM_SQUARE_pth_qstep :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_qstep = cacheProof "ruleNUM_SQUARE_pth_qstep" ctxtWF $
            ruleUNDISCH =<< 
              prove [str| n + BIT1 _0 = m /\
                          m EXP 2 = p /\
                          m + a = BIT0(BIT0 p)
                          ==> (BIT1(BIT1(BIT1 n))) EXP 2 = 
                               BIT1(BIT0(BIT0(BIT0 a))) |]
                (tacABBREV "two = 2" `_THEN`
                 tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN` tacEXPAND "two" `_THEN`
                 tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [ thmADD1, thmLEFT_ADD_DISTRIB
                            , ruleGSYM thmADD_ASSOC ] `_THEN`
                 tacREWRITE [thmMULT_ASSOC] `_THEN` 
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [thmIMP_CONJ] `_THEN`
                 _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN` tacDISCH `_THEN`
                 tacMATCH_MP (ruleMESON [thmEQ_ADD_LCANCEL] 
                                "!m:num. m + n = m + p ==> n = p") `_THEN`
                 tacEXISTS "16 * (n + 1)" `_THEN`
                 tacASM_REWRITE [ thmADD_ASSOC
                                , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
                 tacEXPAND "two" `_THEN` tacREWRITE [thmEXP_2] `_THEN`
                 tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB] `_THEN`
                 tacREWRITE [thmMULT_CLAUSES, thmMULT_ASSOC] `_THEN`
                 tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                             "(8 * n) * NUMERAL p = (8 * NUMERAL p) * n"] `_THEN`
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [runConv (convAC thmADD_AC) =<< toHTm
                             "(n + 16) + p + q + 49 = (n + p + q) + (16 + 49)"] `_THEN`
                 tacREWRITE [ruleGSYM thmADD_ASSOC] `_THEN` 
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [thmADD_ASSOC, thmEQ_ADD_RCANCEL] `_THEN`
                 tacREWRITE [ ruleGSYM thmADD_ASSOC, ruleGSYM thmMULT_2
                            , thmMULT_ASSOC] `_THEN`
                 tacONCE_REWRITE [runConv (convAC thmADD_AC) =<< toHTm
                                    "a + b + c:num = b + a + c"] `_THEN`
                 tacREWRITE [ruleGSYM thmRIGHT_ADD_DISTRIB] `_THEN`
                 tacREWRITE [thmARITH])

        ruleNUM_SQUARE_pth_rec :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_rec = cacheProof "ruleNUM_SQUARE_pth_rec" ctxtWF $
            ruleUNDISCH =<< 
              prove [str| n = l + p * h /\
                          h + l = m /\
                          h EXP 2 = a /\
                          l EXP 2 = c /\
                          m EXP 2 = d /\
                          a + c = e /\
                          e + b = d
                          ==> n EXP 2 = c + p * (b + p * a) |]
                (tacREWRITE [thmIMP_CONJ] `_THEN`
                 _DISCH_THEN tacSUBST1 `_THEN`
                 tacREPLICATE 5 (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
                 tacREWRITE [ thmEXP_2, thmLEFT_ADD_DISTRIB
                            , thmRIGHT_ADD_DISTRIB ] `_THEN`
                 tacREWRITE [thmMULT_AC] `_THEN` 
                 tacCONV (convBINOP convNUM_CANCEL) `_THEN`
                 _DISCH_THEN tacSUBST1 `_THEN` 
                 tacREWRITE [thmRIGHT_ADD_DISTRIB] `_THEN`
                 tacREWRITE [thmMULT_AC] `_THEN` tacREWRITE [thmADD_AC])

        ruleNUM_SQUARE_pth_toom3 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_toom3 = cacheProof "ruleNUM_SQUARE_pth_toom3" ctxtWF $
            do rewrites <- mapM (\ k -> 
                                 do tmSuc <- serve tmSuc'
                                    n <- mkSmallNumeral (k - 1)
                                    th <- runConv (convREWRITE [thmARITH_SUC]) #<< 
                                            mkComb tmSuc n
                                    liftO $ ruleSYM th) [1..5]
               prove [str| h EXP 2 = e /\
                           l EXP 2 = a /\
                           (l + BIT1 _0 * (m + BIT1 _0 * h)) EXP 2 =
                            a +  BIT1 _0 * (b +  BIT1 _0 * (c +  BIT1 _0 * 
                              (d +  BIT1 _0 * e))) /\
                           (l + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * h)) EXP 2 =
                            a + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) *
                              (c + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) * e))) /\
                           (h + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * l)) EXP 2 =
                            e + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) *
                              (c + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) * a)))
                           ==> (l + p * (m + p * h)) EXP 2 =
                                a + p * (b + p * (c + p * (d + p * e))) |] $
                 tacABBREV "two = 2" `_THEN`
                 tacSUBST1 (ruleMESON [defNUMERAL] "_0 = 0") `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN`
                 tacEXPAND "two" `_THEN` tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [thmARITH] `_THEN`
                 _SUBGOAL_THEN 
                   [str| !p x y z. (x + p * (y + p * z)) EXP 2 =
                           x * x + p * (2 * x * y + p * ((2 * x * z + y * y) +
                             p * (2 * y * z + p * z * z))) |]
                 (\ th -> tacREWRITE [th]) `_THENL`
                 [ tacREWRITE [ thmEXP_2, thmMULT_2, thmLEFT_ADD_DISTRIB
                              , thmRIGHT_ADD_DISTRIB ] `_THEN`
                   tacREWRITE [thmMULT_AC] `_THEN` tacREWRITE [thmADD_AC]
                 , tacREWRITE [thmEXP_2]
                 ] `_THEN`
                _MAP_EVERY tacABBREV
                  [ "a':num = l * l", "b' = 2 * l * m", "c' = 2 * l * h + m * m"
                  , "d' = 2 * m * h", "e':num = h * h" ] `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             "2 * m * l = 2 * l * m") `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             "2 * h * l = 2 * l * h") `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             "2 * h * m = 2 * m * h") `_THEN`
                tacASM_REWRITE_NIL `_THEN` tacEXPAND "two" `_THEN`
                _POP_ASSUM_LIST (const _ALL) `_THEN`
                tacASM_CASES "a':num = a" `_THEN` tacASM_REWRITE_NIL `_THEN`
                tacASM_CASES "e':num = e" `_THEN` tacASM_REWRITE_NIL `_THEN`
                _POP_ASSUM_LIST (const _ALL) `_THEN`
                tacREWRITE [thmEQ_ADD_LCANCEL, thmEQ_MULT_LCANCEL] `_THEN`
                tacREWRITE [thmLEFT_ADD_DISTRIB, thmMULT_ASSOC] `_THEN`
                tacREWRITE [thmARITH] `_THEN`
                tacREWRITE [thmMULT_CLAUSES, thmEQ_ADD_LCANCEL] `_THEN`
                tacREWRITE [thmADD_ASSOC, thmEQ_ADD_RCANCEL] `_THEN`
                tacREWRITE [ruleGSYM thmADD_ASSOC] `_THEN` tacDISCH `_THEN`
                _FIRST_ASSUM (tacMP . ruleMATCH_MP 
                              (ruleMESON_NIL [str| b = b' /\ c = c' /\ d = d' 
                                                   ==> 5 * b + c' + d' = 
                                                   5 * b' + c + d |])) `_THEN`
                tacREWRITE [thmLEFT_ADD_DISTRIB, thmMULT_ASSOC] `_THEN`
                tacREWRITE rewrites `_THEN`
                tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
                tacCONV (convLAND convNUM_CANCEL) `_THEN` 
                _DISCH_THEN tacSUBST_ALL `_THEN`
                _FIRST_ASSUM (tacMP . ruleMATCH_MP 
                              (ruleMESON_NIL [str| b = b' /\ c = c' /\ d = d' ==>
                                                   b + d':num = b' + d /\ 
                                                   4 * b + d' = 
                                                   4 * b' + d |])) `_THEN`
                tacREWRITE [thmLEFT_ADD_DISTRIB, thmMULT_ASSOC] `_THEN`
                tacREWRITE (init rewrites) `_THEN`
                tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
                tacCONV (convLAND (convBINOP convNUM_CANCEL)) `_THEN`
                tacREWRITE [ruleGSYM thmMULT_2] `_THEN` 
                tacONCE_REWRITE [thmADD_SYM] `_THEN`
                tacREWRITE [ruleGSYM =<< liftM (!! 4) 
                            (ruleCONJUNCTS thmMULT_CLAUSES)] `_THEN`
                tacSIMP [thmEQ_MULT_LCANCEL, thmNOT_SUC]

        ruleNUM_SQUARE_pth_even3 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_even3 = cacheProof "ruleNUM_SQUARE_pth_even3" ctxtWF .
            prove [str| m EXP 2 = n <=>
                       (BIT0(BIT0(BIT0 m))) EXP 2 = 
                        BIT0(BIT0(BIT0(BIT0(BIT0(BIT0 n))))) |] $
              tacABBREV "two = 2" `_THEN`
              tacREWRITE [thmBIT0] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacEXPAND "two" `_THEN` tacREWRITE [thmEXP_2] `_THEN`
              tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                          [str| (2 * 2 * 2 * m) * 2 * 2 * 2 * m = 
                                  2 * 2 * 2 * 2 * 2 * 2 * m * m |]] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

convNUM :: WFCtxt thry => Conversion cls thry
convNUM = Conv $ \ tm ->
    do tmSUC <- serve tmSuc'
       let n = fromJust (destNumeral tm) - 1
       if n < 0
          then fail "convNUM"
          else do tm' <- mkNumeral n
                  th <- runConv convNUM_SUC #<< mkComb tmSUC tm'
                  liftO $ ruleSYM th

-- Misc utility stuff
ruleAP_BIT0 :: WFCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleAP_BIT0 th = 
    do tm <- serve tmBIT0'
       liftO $ primMK_COMB (primREFL tm) th

ruleAP_BIT1 :: WFCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleAP_BIT1 th = 
    do tm <- serve tmBIT1'
       liftO $ primMK_COMB (primREFL tm) th

ruleQUICK_PROVE_HYP :: HOLThm -> HOLThm -> Either String HOLThm
ruleQUICK_PROVE_HYP ath bth =
    primEQ_MP (primDEDUCT_ANTISYM ath bth) ath

destRawNumeral :: HOLTerm -> Maybe Int
destRawNumeral (BIT1 t) =
    do t' <- destRawNumeral t
       return $! 2 * t' + 1
destRawNumeral (BIT0 t) =
    do t' <- destRawNumeral t
       return $! 2 * t'
destRawNumeral (Const "_0" _) =
    return 0
destRawNumeral _ = Nothing

bitcounts :: HOLTerm -> Maybe (Int, Int)
bitcounts = bctr 0 0
  where bctr :: Int -> Int -> HOLTerm -> Maybe (Int, Int)
        bctr w z (Const "_0" _) = Just (w, z)
        bctr w z (BIT0 t) = bctr w (succ z) t
        bctr w z (BIT1 t) = bctr (succ w) z t
        bctr _ _ _ = Nothing

wellformed :: HOLTerm -> Bool
wellformed (Const "_0" _) = True
wellformed (BIT0 t) = wellformed t
wellformed (BIT1 t) = wellformed t
wellformed _ = False

orderrelation :: HOLTerm -> HOLTerm -> Maybe Ordering
orderrelation mtm ntm
    | mtm == ntm = if wellformed mtm then Just EQ else Nothing
    | otherwise =
        case (mtm, ntm) of
          (Const "_0" _, Const "_0" _) -> Just EQ
          (Const "_0" _, _) ->
              if wellformed ntm then Just LT else Nothing
          (_, Const "_0" _) ->
              if wellformed ntm then Just GT else Nothing
          (BIT0 mt, BIT0 nt) ->
              orderrelation mt nt
          (BIT1 mt, BIT1 nt) ->
              orderrelation mt nt
          (BIT0 mt, BIT1 nt) ->
              Just $ if orderrelation mt nt == Just GT then GT else LT
          (BIT1 mt, BIT0 nt) ->
              Just $ if orderrelation mt nt == Just LT then LT else EQ
          _ -> Nothing

doublebn :: WFCtxt thry => HOLTerm -> HOL cls thry HOLTerm
doublebn tm@(Const "_0" _) = return tm
doublebn tm = 
    do tmBIT0 <- serve tmBIT0'
       liftO $ mkComb tmBIT0 tm

subbn :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
subbn = subbnRec
  where subbnRec :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
        subbnRec mtm (Const "_0" _) = 
            return mtm
        subbnRec (BIT0 mt) (BIT0 nt) =
            doublebn =<< subbnRec mt nt
        subbnRec (BIT1 mt) (BIT1 nt) =
            doublebn =<< subbnRec mt nt
        subbnRec (BIT1 mt) (BIT0 nt) =
            do tmBIT1 <- serve tmBIT1'
               tm' <- subbnRec mt nt
               liftO $ mkComb tmBIT1 tm'
        subbnRec (BIT0 mt) (BIT1 nt) =
            do tmBIT1 <- serve tmBIT1'
               tm' <- sbcbn mt nt
               liftO $ mkComb tmBIT1 tm'
        subbnRec _ _ = fail "subbn"

sbcbn :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
sbcbn = sbcbnRec
  where sbcbnRec :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
        sbcbnRec (BIT0 mt) nt@(Const "_0" _) =
            do tmBIT1 <- serve tmBIT1'
               tm' <- sbcbnRec mt nt
               liftO $ mkComb tmBIT1 tm'
        sbcbnRec (BIT1 mt) (Const "_0" _) =
            doublebn mt
        sbcbnRec (BIT0 mt) (BIT0 nt) =
            do tmBIT1 <- serve tmBIT1'
               tm' <- sbcbnRec mt nt
               liftO $ mkComb tmBIT1 tm'
        sbcbnRec (BIT1 mt) (BIT1 nt) =
            do tmBIT1 <- serve tmBIT1'
               tm' <- sbcbnRec mt nt
               liftO $ mkComb tmBIT1 tm'
        sbcbnRec (BIT1 mt) (BIT0 nt) =
            doublebn =<< subbn mt nt
        sbcbnRec (BIT0 mt) (BIT1 nt) =
            doublebn =<< sbcbnRec mt nt
        sbcbnRec _ _ = fail "sbcbn"

topsplit :: HOLTerm -> Maybe (Int, HOLTerm)
topsplit n@(Const "_0" _) = Just (0, n)
topsplit (BIT1 n@(Const "_0" _)) = Just (1, n)
topsplit (BIT0 (BIT1 n@(Const "_0" _))) = Just (2, n)
topsplit (BIT1 (BIT1 n@(Const "_0" _))) = Just (3, n)
topsplit (BIT0 (BIT0 (BIT1 n@(Const "_0" _)))) = Just (4, n)
topsplit (BIT1 (BIT0 (BIT1 n@(Const "_0" _)))) = Just (5, n)
topsplit (BIT0 (BIT1 (BIT1 n@(Const "_0" _)))) = Just (6, n)
topsplit (BIT1 (BIT1 (BIT1 n@(Const "_0" _)))) = Just (7, n)
topsplit (BIT0 (BIT0 (BIT0 (BIT0 n)))) = Just (0, n)
topsplit (BIT1 (BIT0 (BIT0 (BIT0 n)))) = Just (1, n)
topsplit (BIT0 (BIT1 (BIT0 (BIT0 n)))) = Just (2, n)
topsplit (BIT1 (BIT1 (BIT0 (BIT0 n)))) = Just (3, n)
topsplit (BIT0 (BIT0 (BIT1 (BIT0 n)))) = Just (4, n)
topsplit (BIT1 (BIT0 (BIT1 (BIT0 n)))) = Just (5, n)
topsplit (BIT0 (BIT1 (BIT1 (BIT0 n)))) = Just (6, n)
topsplit (BIT1 (BIT1 (BIT1 (BIT0 n)))) = Just (7, n)
topsplit (BIT0 (BIT0 (BIT0 (BIT1 n)))) = Just (8, n)
topsplit (BIT1 (BIT0 (BIT0 (BIT1 n)))) = Just (9, n)
topsplit (BIT0 (BIT1 (BIT0 (BIT1 n)))) = Just (10, n)
topsplit (BIT1 (BIT1 (BIT0 (BIT1 n)))) = Just (11, n)
topsplit (BIT0 (BIT0 (BIT1 (BIT1 n)))) = Just (12, n)
topsplit (BIT1 (BIT0 (BIT1 (BIT1 n)))) = Just (13, n)
topsplit (BIT0 (BIT1 (BIT1 (BIT1 n)))) = Just (14, n)
topsplit (BIT1 (BIT1 (BIT1 (BIT1 n)))) = Just (15, n)
topsplit _ = Nothing