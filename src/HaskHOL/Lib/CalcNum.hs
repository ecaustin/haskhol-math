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
    , convNUM_SUB
    , convNUM_PRE
    , convNUM_FACT
    , convNUM_GT
    , convNUM_GE
    , convNUM_ODD
    , convNUM_DIV
    , convNUM_MOD
    , convNUM_MAX
    , convNUM_MIN
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
    , convNUM_RED
    , convNUM_REDUCE
    ) where

import HaskHOL.Core hiding (pattern (:=))
import HaskHOL.Deductive

import HaskHOL.Lib.Nums hiding (pattern SUC)
import qualified HaskHOL.Lib.Nums as Nums (pattern SUC)
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF

import HaskHOL.Lib.CalcNum.Pre
import HaskHOL.Lib.CalcNum.Pre2

pattern SUC :: HOLTerm -> HOLTerm
pattern SUC x <- Comb Nums.SUC (NUMERAL x)

pattern BIN_OP :: Text -> HOLTerm -> HOLTerm -> HOLTerm
pattern BIN_OP str x y <- Binary str (NUMERAL x) (NUMERAL y)

pattern (:+) :: HOLTerm -> HOLTerm -> HOLTerm
pattern x :+ y <- BIN_OP "+" x y
pattern (:*) :: HOLTerm -> HOLTerm -> HOLTerm
pattern x :* y <- BIN_OP "*" x y
pattern (:<=) :: HOLTerm -> HOLTerm -> HOLTerm
pattern x :<= y <- BIN_OP "<=" x y
pattern (:=) :: HOLTerm -> HOLTerm -> HOLTerm
pattern x := y <- BIN_OP "=" x y
pattern (:<) :: HOLTerm -> HOLTerm -> HOLTerm
pattern x :< y <- BIN_OP "<" x y

tmA, tmB, tmC, tmD, tmE, tmH, tmL, tmMul, tmSUC :: WFCtxt thry => HOL cls thry HOLTerm
tmA = serve [wf| a:num |]
tmB = serve [wf| b:num |]
tmC = serve [wf| c:num |]
tmD = serve [wf| d:num |]
tmE = serve [wf| e:num |]
tmH = serve [wf| h:num |]
tmL = serve [wf| l:num |]
tmMul = serve [wf| (*) |]
tmSUC = serve [wf| SUC |]

-- numeral conversions
convNUM_EVEN :: WFCtxt thry => Conversion cls thry
convNUM_EVEN = Conv $ \ tm ->
    do (tth, rths) <- ruleCONJ_PAIR thmARITH_EVEN
       runConv (convGEN_REWRITE id [tth] `_THEN` convGEN_REWRITE id [rths]) tm

convNUM_ODD :: WFCtxt thry => Conversion cls thry
convNUM_ODD = Conv $ \ tm ->
    do (tth, rths) <- ruleCONJ_PAIR thmARITH_ODD
       runConv (convGEN_REWRITE id [tth] `_THEN` convGEN_REWRITE id [rths]) tm

convNUM_SUC ::  WFCtxt thry => Conversion cls thry
convNUM_SUC = Conv $ \ tm -> note "convNUM_SUC" $
    case tm of
      (SUC mtm) ->
          if wellformed mtm
          then do th1 <- ruleNUM_ADC tmZero mtm
                  ntm <- rand $ concl th1
                  th2 <- primINST [(tmM, mtm), (tmN, ntm)] convNUM_SUC_pth
                  primEQ_MP th2 th1
          else fail "not wellformed."
      _ -> fail "not a SUC term."
  where convNUM_SUC_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SUC_pth = cacheProof "convNUM_SUC_pth" ctxtWF .
            prove [txt| SUC(_0 + m) = n <=> SUC(NUMERAL m) = NUMERAL n |] $
              tacBINOP `_THEN` tacMESON [defNUMERAL, thmADD_CLAUSES]

convNUM_ADD :: WFCtxt thry => Conversion cls thry
convNUM_ADD = Conv $ \ tm -> note "convNUM_ADD" $
    case tm of
      (mtm :+ ntm) ->
          if wellformed mtm && wellformed ntm
          then do th1 <- ruleNUM_ADD mtm ntm
                  ptm <- rand $ concl th1
                  th2 <- primINST [ (tmM, mtm), (tmN, ntm)
                                  , (tmP, ptm) ] convNUM_ADD_pth
                  primEQ_MP th2 th1
          else fail "not wellformed."
      _ -> fail "not an addition term."
  where convNUM_ADD_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_ADD_pth = cacheProof "convNUM_ADD_pth" ctxtWF $
            ruleMESON [defNUMERAL] 
              [txt| m + n = p <=> NUMERAL m + NUMERAL n = NUMERAL p |]

convNUM_MULT :: WFCtxt thry => Conversion cls thry
convNUM_MULT = Conv $ \ tm -> note "convNUM_MULT" $
    case tm of
      (mtm :* ntm)
          | mtm == ntm ->
              do th1 <- ruleNUM_SQUARE mtm
                 ptm <- rand $ concl th1
                 th2 <- primINST [(tmM, mtm), (tmP, ptm)] convNUM_MULT_pth2
                 primEQ_MP th2 th1
          | otherwise ->
              do (w1, z1) <- bitcounts mtm
                 (w2, z2) <- bitcounts ntm
                 th1 <- ruleNUM_MUL (w1+z1) (w2+z2) mtm ntm
                 ptm <- rand $ concl th1
                 th2 <- primINST [ (tmM, mtm), (tmN, ntm)
                                 , (tmP, ptm) ] convNUM_MULT_pth1
                 primEQ_MP th2 th1
      _ -> fail "not a multiplication term."
  where convNUM_MULT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_MULT_pth1 = cacheProof "convNUM_MULT_pth1" ctxtWF $
            ruleMESON [defNUMERAL] 
              [txt| m * n = p <=> NUMERAL m * NUMERAL n = NUMERAL p |]

        convNUM_MULT_pth2 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_MULT_pth2 = cacheProof "convNUM_MULT_pth2" ctxtWF $
            ruleMESON [defNUMERAL, thmEXP_2] 
              [txt| m EXP 2 = p <=> NUMERAL m * NUMERAL m = NUMERAL p |]

convNUM_LE :: WFCtxt thry => Conversion cls thry
convNUM_LE = Conv $ \ tm -> note "convNUM_LE" $
    case tm of
      (mtm :<= ntm) ->
          case orderrelation mtm ntm of
            Just EQ -> primINST [(tmN, ntm)] convNUM_LE_rth
            Just LT ->
                do dtm <- subbn ntm mtm
                   th1 <- ruleNUM_ADD dtm mtm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_LE_pth
                   ruleQUICK_PROVE_HYP th1 th2
            _ ->
                do dtm <- sbcbn mtm ntm
                   th1 <- ruleNUM_ADC dtm ntm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_LE_qth
                   ruleQUICK_PROVE_HYP th1 th2
      _ -> fail "not an LE term."
  where convNUM_LE_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_pth = cacheProof "convNUM_LE_pth" ctxtWF .
            ruleUNDISCH $ 
              prove [txt| m + n = p ==> ((NUMERAL n <= NUMERAL p) <=> T) |]
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [defNUMERAL] `_THEN`
                 tacMESON [thmLE_ADD, thmADD_SYM])

        convNUM_LE_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_qth = cacheProof "convNUM_LE_qth" ctxtWF .
            ruleUNDISCH $ 
              prove [txt| SUC(m + p) = n ==> (NUMERAL n <= NUMERAL p <=> F) |]
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, thmNOT_LE
                            , thmADD_CLAUSES, thmLT_EXISTS ] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_LE_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LE_rth = cacheProof "convNUM_LE_rth" ctxtWF .
            prove [txt| NUMERAL n <= NUMERAL n <=> T |] $
              tacREWRITE [thmLE_REFL]

convNUM_EQ :: WFCtxt thry => Conversion cls thry
convNUM_EQ = Conv $ \ tm -> note "convNUM_EQ" $
    case tm of
      (mtm := ntm) ->
          case orderrelation mtm ntm of
            Just EQ -> primINST [(tmN, ntm)] convNUM_EQ_rth
            Just LT ->
                do dtm <- sbcbn ntm mtm
                   th1 <- ruleNUM_ADC dtm mtm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_EQ_pth
                   ruleQUICK_PROVE_HYP th1 th2
            _ ->
                do dtm <- sbcbn mtm ntm
                   th1 <- ruleNUM_ADC dtm ntm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_EQ_qth
                   ruleQUICK_PROVE_HYP th1 th2
                                      
      _ -> fail "not an equation."
  where convNUM_EQ_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_pth = cacheProof "convNUM_EQ_pth" ctxtWF .
            ruleUNDISCH $ 
              prove [txt| SUC(m + n) = p ==> ((NUMERAL n = NUMERAL p) <=> F) |]
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, ruleGSYM thmLE_ANTISYM
                            , thmDE_MORGAN ] `_THEN`
                 tacREWRITE [thmNOT_LE, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_EQ_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_qth = cacheProof "convNUM_EQ_qth" ctxtWF .
            ruleUNDISCH $
              prove [txt| SUC(m + p) = n ==> ((NUMERAL n = NUMERAL p) <=> F) |]
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [ defNUMERAL, ruleGSYM thmLE_ANTISYM
                            , thmDE_MORGAN ] `_THEN`
                 tacREWRITE [thmNOT_LE, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_EQ_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EQ_rth = cacheProof "convNUM_EQ_rth" ctxtWF $
            prove [txt| (NUMERAL n = NUMERAL n) <=> T |] tacREWRITE_NIL

convNUM_EXP :: WFCtxt thry =>Conversion cls thry
convNUM_EXP = Conv $ \ tm -> note "convNUM_EXP" $
    do th <- runConv (convGEN_REWRITE id [convNUM_EXP_tth]) tm
       (lop, r) <- destComb =<< rand (concl th)
       (_, l) <- destComb lop
       if not (wellformed l && wellformed r)
          then fail "not wellformed."
          else do th' <- ruleNUM_EXP_CONV l r
                  tm' <- rand (concl th')
                  primTRANS (primTRANS th th') $
                    primINST [(tmM, tm')] convNUM_EXP_fth
  where ruleNUM_EXP_CONV :: WFCtxt thry => HOLTerm -> HOLTerm
                         -> HOL cls thry HOLThm
        ruleNUM_EXP_CONV l ZERO = primINST [(tmM, l)] convNUM_EXP_pth
        ruleNUM_EXP_CONV l (BIT0 r') =
            do th1 <- ruleNUM_EXP_CONV l r'
               tm1 <- rand $ concl th1
               th2 <- runConv convNUM_MULT' $ mkBinop tmMul tm1 tm1
               tm2 <- rand $ concl th2
               th3 <- primINST [ (tmM, l), (tmN, r'), (tmP, tm1)
                               , (tmB, tm2), (tmA, tm2) ] convNUM_EXP_pth0
               ruleMP (ruleMP th3 th1) th2
        ruleNUM_EXP_CONV l (Comb _ r') =
            do th1 <- ruleNUM_EXP_CONV l r'
               tm1 <- rand $ concl th1
               th2 <- runConv convNUM_MULT' $ mkBinop tmMul tm1 tm1
               tm2 <- rand $ concl th2
               th3 <- runConv convNUM_MULT' $ mkBinop tmMul l tm2
               tm3 <- rand $ concl th3
               th4 <- primINST [ (tmM, l), (tmN, r'), (tmP, tm1)
                               , (tmB, tm2), (tmA, tm3) ] convNUM_EXP_pth1
               ruleMP (ruleMP (ruleMP th4 th1) th2) th3
        ruleNUM_EXP_CONV _ _ = fail "ruleNUM_EXP_CONV"
        convNUM_MULT' :: WFCtxt thry => Conversion cls thry
        convNUM_MULT' = Conv $ \ tm -> note "convNUM_MULT'" $
            case tm of
              (mtm :* ntm)
                  | mtm == ntm ->
                      do th1 <- ruleNUM_SQUARE mtm
                         ptm <- rand $ concl th1
                         th2 <- primINST [(tmM, mtm), (tmP, ptm)] 
                                  convNUM_EXP_pth_refl
                         primEQ_MP th2 th1
                  | otherwise ->
                      do (w1, z1) <- bitcounts mtm
                         (w2, z2) <- bitcounts ntm
                         ruleNUM_MUL (w1+z1) (w2+z2) mtm ntm
              _ -> fail "not a multiplication."

        convNUM_EXP_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth0 = cacheProof "convNUM_EXP_pth0" ctxtWF .
            prove [txt| (m EXP n = p) ==> (p * p = a) ==> 
                        (m EXP (BIT0 n) = a) |] $
              _REPEAT (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
              tacREWRITE [thmBIT0, thmEXP_ADD]

        convNUM_EXP_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth1 = cacheProof "convNUM_EXP_pth1" ctxtWF .
            prove [txt| (m EXP n = p) ==> (p * p = b) ==> (m * b = a) ==>
                        (m EXP (BIT1 n) = a) |] $
              _REPEAT (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
              tacREWRITE [thmBIT1, thmEXP_ADD, defEXP]

        convNUM_EXP_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_pth = cacheProof "convNUM_EXP_pth" ctxtWF .
            prove [txt| m EXP _0 = BIT1 _0 |] $
              tacMP (ruleCONJUNCT1 defEXP) `_THEN` 
              tacREWRITE [defNUMERAL, thmBIT1] `_THEN`
              _DISCH_THEN tacMATCH_ACCEPT

        convNUM_EXP_tth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_tth = cacheProof "convNUM_EXP_tth" ctxtWF .
            prove [txt| (NUMERAL m) EXP (NUMERAL n) = m EXP n |] $
              tacREWRITE [defNUMERAL]

        convNUM_EXP_fth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_EXP_fth = cacheProof "convNUM_EXP_fth" ctxtWF .
            prove [txt| m = NUMERAL m |] $ tacREWRITE [defNUMERAL]

        convNUM_EXP_pth_refl :: WFCtxt thry 
                             => HOL cls thry HOLThm
        convNUM_EXP_pth_refl = cacheProof "convNUM_EXP_pth_refl" ctxtWF $
            ruleMESON [thmEXP_2] [txt| m EXP 2 = p <=> m * m = p |]

convNUM_LT :: WFCtxt thry => Conversion cls thry
convNUM_LT = Conv $ \ tm -> note "convNUM_LT" $
    case tm of
      (mtm :< ntm) ->
          case orderrelation mtm ntm of
            Just EQ -> primINST [(tmN, ntm)] convNUM_LT_rth
            Just LT ->
                do dtm <- sbcbn ntm mtm
                   th1 <- ruleNUM_ADC dtm mtm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_LT_pth
                   ruleQUICK_PROVE_HYP th1 th2
            _ ->
                do dtm <- subbn mtm ntm
                   th1 <- ruleNUM_ADD dtm ntm
                   th2 <- primINST [ (tmM, dtm), (tmN, mtm)
                                   , (tmP, ntm) ] convNUM_LT_qth
                   ruleQUICK_PROVE_HYP th1 th2            
      _ -> fail "not a LT term."
  where convNUM_LT_pth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_pth = cacheProof "convNUM_LT_pth" ctxtWF .
            ruleUNDISCH $
              prove [txt| SUC(m + n) = p ==> ((NUMERAL n < NUMERAL p) <=> T) |]
                (tacREWRITE [defNUMERAL, thmLT_EXISTS, thmADD_CLAUSES] `_THEN`
                 tacMESON [thmADD_SYM])

        convNUM_LT_qth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_qth = cacheProof "convNUM_LT_qth" ctxtWF .
            ruleUNDISCH $
              prove [txt| m + p = n ==> (NUMERAL n < NUMERAL p <=> F) |]
                (_DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 tacREWRITE [thmNOT_LT, defNUMERAL] `_THEN`
                 tacMESON [thmLE_ADD, thmADD_SYM])

        convNUM_LT_rth :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_LT_rth = cacheProof "convNUM_LT_rth" ctxtWF .
            prove [txt| NUMERAL n < NUMERAL n <=> F |] $ tacMESON[thmLT_REFL]
                           
ruleNUM_ADD :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLThm
ruleNUM_ADD mtm ntm = note "ruleNUM_ADD" $
    do (mLo, mHi) <- topsplit mtm
       (nLo, nHi) <- topsplit ntm
       let mInd = case mHi of
                    ZERO -> mLo
                    _ -> mLo + 16
           nInd = case nHi of
                    ZERO -> nLo
                    _ -> nLo + 16
           ind = 32 * mInd + nInd
       clauses <- addClauses
       let th1 = clauses !! ind
       flags <- addFlags
       case flags !! ind of
         0 -> primINST [(tmM, mHi)] th1
         1 -> primINST [(tmN, nHi)] th1
         2 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADD mHi nHi
                 th3 <- primINST [(tmM, mHi), (tmN, nHi), (tmP, ptm)] th1
                 primEQ_MP th3 th2
         3 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADC mHi nHi
                 th3 <- primINST [(tmM, mHi), (tmN, nHi), (tmP, ptm)] th1
                 primEQ_MP th3 th2
         _ -> fail "bad flag."

ruleNUM_ADC :: (WFCtxt thry, HOLTermRep tm1 cls thry, HOLTermRep tm2 cls thry) 
            => tm1 -> tm2 -> HOL cls thry HOLThm
ruleNUM_ADC ptm1 ptm2 = note "ruleNUM_ADC" $
    do mtm <- toHTm ptm1
       ntm <- toHTm ptm2 
       (mLo, mHi) <- topsplit mtm
       (nLo, nHi) <- topsplit ntm
       let mInd = case mHi of
                    ZERO -> mLo
                    _ -> mLo + 16
           nInd = case nHi of
                    ZERO -> nLo
                    _ -> nLo + 16
           ind = 32 * mInd + nInd
       clauses <- adcClauses
       flags <- adcFlags
       let th1 = clauses !! ind
       case flags !! ind of
         0 -> primINST [(tmM, mHi)] th1
         1 -> primINST [(tmN, nHi)] th1
         2 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADD mHi nHi
                 th3 <- primINST [(tmM, mHi), (tmN, nHi), (tmP, ptm)] th1
                 primEQ_MP th3 th2
         3 -> do th2@(Thm _ (Comb _ ptm)) <- ruleNUM_ADC mHi nHi
                 th3 <- primINST [(tmM, mHi), (tmN, nHi), (tmP, ptm)] th1
                 primEQ_MP th3 th2
         _ -> fail "bad flag."


ruleNUM_MUL_pth_0 :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_0 = 
    cacheProofs ["ruleNUM_MUL_pth_0l", "ruleNUM_MUL_pth_0r"] ctxtWF $
      do th <- prove [txt| _0 * n = _0 /\ m * _0 = _0 |] $
                 tacMESON [defNUMERAL, thmMULT_CLAUSES]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]

ruleNUM_MUL_pth_1 :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_1 = 
    cacheProofs ["ruleNUM_MUL_pth_1l", "ruleNUM_MUL_pth_1r"] ctxtWF $
      do th <- prove [txt| (BIT1 _0) * n = n /\ m * (BIT1 _0) = m |] $
                 tacMESON [defNUMERAL, thmMULT_CLAUSES]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]
    
ruleNUM_MUL_pth_even :: WFCtxt thry => [HOL cls thry HOLThm]
ruleNUM_MUL_pth_even = 
    cacheProofs ["ruleNUM_MUL_pth_evenl", "ruleNUM_MUL_pth_evenr"] ctxtWF $
      do th <- prove [txt| (m * n = p <=> (BIT0 m) * n = BIT0 p) /\
                           (m * n = p <=> m * BIT0 n = BIT0 p) |] $
                 tacREWRITE [thmBIT0] `_THEN` 
                 tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                               [txt| m * 2 * n = 2 * m * n |]
                            ] `_THEN`
                 tacREWRITE [ ruleGSYM thmMULT_ASSOC
                            , thmEQ_MULT_LCANCEL, thmARITH_EQ ]
         (th1, th2) <- ruleCONJ_PAIR th
         return [th1, th2]


ruleNUM_MUL :: WFCtxt thry => Int -> Int -> HOLTerm 
            -> HOLTerm -> HOL cls thry HOLThm
ruleNUM_MUL _ _ ZERO tm' = primINST [(tmN, tm')] (ruleNUM_MUL_pth_0 !! 0)
ruleNUM_MUL _ _ tm ZERO = primINST [(tmM, tm)] (ruleNUM_MUL_pth_0 !! 1)
ruleNUM_MUL _ _ (BIT1 ZERO) tm' = primINST [(tmN, tm')] (ruleNUM_MUL_pth_1 !! 0)
ruleNUM_MUL _ _ tm (BIT1 ZERO) = primINST [(tmM, tm)] (ruleNUM_MUL_pth_1 !! 1)
ruleNUM_MUL k l (BIT0 mtm) tm' =
    do th0 <- ruleNUM_MUL (k - 1) l mtm tm'
       tm0 <- rand $ concl th0
       th1 <- primINST [ (tmM, mtm), (tmN, tm')
                       , (tmP, tm0) ] (ruleNUM_MUL_pth_even !! 0)
       primEQ_MP th1 th0
ruleNUM_MUL k l tm (BIT0 ntm) =
    do th0 <- ruleNUM_MUL k (l - 1) tm ntm
       tm0 <- rand $ concl th0
       th1 <- primINST [ (tmM, tm), (tmN, ntm)
                       , (tmP, tm0) ] (ruleNUM_MUL_pth_even !! 1)
       primEQ_MP th1 th0
ruleNUM_MUL k l tm@(BIT1 mtm) tm'@(BIT1 ntm)
    | k <= 50 || l <= 50 || k * k < l || l * l < k =
        case (mtm, ntm) of
          (BIT1 (BIT1 _), _) ->
              do th1 <- ruleNUM_ADC tmZero tm
                 ptm <- rand $ concl th1
                 th2 <- ruleNUM_MUL k l ptm tm'
                 tm2 <- rand $ concl th2
                 atm <- subbn tm2 tm'
                 th3 <- primINST [ (tmM, tm), (tmN, tm'), (tmP, ptm)
                                 , (tmA, atm) ] ruleNUM_MUL_pth_recodel
                 th4 <- rulePROVE_HYP th1 th3
                 th5 <- ruleNUM_ADD atm tm'
                 primEQ_MP th4 . primTRANS th2 $ ruleSYM th5
          (_, BIT1 (BIT1 _)) ->
              do th1 <- ruleNUM_ADC tmZero tm'
                 ptm <- rand $ concl th1
                 th2 <- ruleNUM_MUL k l tm ptm
                 tm2 <- rand $ concl th2
                 atm <- subbn tm2 tm
                 th3 <- primINST [ (tmM, tm), (tmN, tm'), (tmP, ptm)
                                 , (tmA, atm) ] ruleNUM_MUL_pth_recoder
                 th4 <- rulePROVE_HYP th1 th3
                 th5 <- ruleNUM_ADD atm tm
                 primEQ_MP th4 . primTRANS th2 $ ruleSYM th5
          _
            |  k <= l -> 
                do th0 <- ruleNUM_MUL (k - 1) l mtm tm'
                   ptm <- rand $ concl th0 
                   pth' <- primINST [ (tmM, mtm), (tmN, tm')
                                    , (tmP, ptm) ] (ruleNUM_MUL_pth_odd !! 0)
                   th1 <- primEQ_MP pth' th0
                   tm1 <- lHand =<< rand (concl th1)
                   th2 <- ruleNUM_ADD tm1 tm'
                   primTRANS th1 th2
              | otherwise ->
                  do th0 <- ruleNUM_MUL k (l - 1) tm ntm
                     ptm <- rand $ concl th0
                     pth' <- primINST [ (tmM, tm), (tmN, ntm)
                                      , (tmP, ptm) ] (ruleNUM_MUL_pth_odd !! 1)
                     th1 <- primEQ_MP pth' th0
                     tm1 <- lHand =<< rand (concl th1)
                     th2 <- ruleNUM_ADD tm1 tm
                     primTRANS th1 th2
    | otherwise =
        do mval <- destRawNumeral mtm
           nval <- destRawNumeral ntm
           if nval <= mval
              then do n <- mkNumeral (mval - nval)
                      ptm <- rand n
                      th2 <- ruleNUM_ADD ntm ptm
                      th3 <- ruleNUM_ADC mtm ntm
                      atm <- rand $ concl th3
                      th4 <- ruleNUM_SQUARE ptm
                      btm <- rand $ concl th4
                      th5 <- ruleNUM_SQUARE atm
                      ctm <- rand $ concl th5
                      dtm <- subbn ctm btm
                      th6 <- ruleNUM_ADD btm dtm
                      th1 <- primINST [ (tmA, atm), (tmB, btm)
                                      , (tmC, ctm), (tmD, dtm)
                                      , (tmM, mtm), (tmN, ntm)
                                      , (tmP, ptm) ] (ruleNUM_MUL_pth_oo !! 0)
                      th7 <- foldr1M ruleCONJ [th2, th3, th4, th5, th6]
                      ruleQUICK_PROVE_HYP th7 th1
             else do n <- mkNumeral (nval - mval)
                     ptm <- rand n
                     th2 <- ruleNUM_ADD mtm ptm
                     th3 <- ruleNUM_ADC ntm mtm
                     atm <- rand $ concl th3
                     th4 <- ruleNUM_SQUARE ptm
                     btm <- rand $ concl th4
                     th5 <- ruleNUM_SQUARE atm
                     ctm <- rand $ concl th5
                     dtm <- subbn ctm btm
                     th6 <- ruleNUM_ADD btm dtm
                     th1 <- primINST [ (tmA, atm), (tmB, btm)
                                     , (tmC, ctm), (tmD, dtm)
                                     , (tmM, mtm), (tmN, ntm)
                                     , (tmP, ptm) ] (ruleNUM_MUL_pth_oo !! 1)
                     th7 <- foldr1M ruleCONJ [th2, th3, th4, th5, th6]
                     ruleQUICK_PROVE_HYP th7 th1
  where ruleNUM_MUL_pth_oo :: WFCtxt thry => [HOL cls thry HOLThm]
        ruleNUM_MUL_pth_oo = 
            cacheProofs ["ruleNUM_MUL_pth_oo1", "ruleNUM_MUL_pth_oo2"] ctxtWF $
                do th1 <- prove [txt| n + p = m /\ SUC(m + n) = a /\ 
                                      p EXP 2 = b /\ a EXP 2 = c /\ b + d = c
                                      ==> ((BIT1 m) * (BIT1 n) = d) |] $ 
                            tacABBREV [txt| two = 2 |] `_THEN` 
                            tacREWRITE [thmBIT1, thmIMP_CONJ] `_THEN`
                            _FIRST_X_ASSUM (tacSUBST1 . ruleSYM) `_THEN`
                            tacREWRITE [thmEXP_2, ruleGSYM thmMULT_2] `_THEN`
                            tacREPLICATE 4 (_DISCH_THEN 
                                            (tacSUBST1 . ruleSYM)) `_THEN`
                            tacREWRITE [thmADD1, runConv (convAC thmADD_AC) =<< 
                                       toHTm [txt| ((n + p) + n) + 1 = 
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
                   th3 <- primINST [(tmM, tmN), (tmN, tmM)] th2
                   th4 <- rulePURE_ONCE_REWRITE [thmMULT_SYM] th3
                   return [th2, th4]

        ruleNUM_MUL_pth_odd :: WFCtxt thry => [HOL cls thry HOLThm]
        ruleNUM_MUL_pth_odd = 
          cacheProofs ["ruleNUM_MUL_pth_oddl", "ruleNUM_MUL_pth_oddr"] ctxtWF $
            do th <- prove [txt| (m * n = p <=> BIT1 m * n = BIT0 p + n) /\
                                 (m * n = p <=> m * BIT1 n = BIT0 p + m) |] $
                       tacREWRITE [thmBIT0, thmBIT1] `_THEN` 
                       tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                       tacREWRITE [thmMULT_CLAUSES] `_THEN`
                       tacREWRITE [ruleMESON [thmMULT_AC, thmADD_SYM]
                                     [txt| m + m * 2 * n = 2 * m * n + m |]
                                  ] `_THEN`
                       tacREWRITE [ ruleGSYM thmMULT_ASSOC
                                  , thmEQ_MULT_LCANCEL
                                  , thmEQ_ADD_RCANCEL ] `_THEN`
                       tacREWRITE [thmARITH_EQ]
               (th1, th2) <- ruleCONJ_PAIR th
               return [th1, th2]

        ruleNUM_MUL_pth_recodel :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_recodel = cacheProof "ruleNUM_MUL_pth_recodel" ctxtWF .
            ruleUNDISCH_ALL . prove [txt| SUC(_0 + m) = p ==> 
                                          (p * n = a + n <=> m * n = a) |] $
              tacSUBST1 (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
              _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
              tacREWRITE [thmADD_CLAUSES, thmMULT_CLAUSES, thmEQ_ADD_RCANCEL]

        ruleNUM_MUL_pth_recoder :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_MUL_pth_recoder = cacheProof "ruleNUM_MUL_pth_recoder" ctxtWF $
            do th <- prove [txt| SUC(_0 + n) = p ==> 
                                 (m * p = a + m <=> m * n = a) |] $
                       tacONCE_REWRITE [thmMULT_SYM] `_THEN`
                       tacSUBST1 
                         (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
                       _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                       tacREWRITE [thmADD_CLAUSES, thmMULT_CLAUSES
                                  , thmEQ_ADD_RCANCEL]
               ruleUNDISCH_ALL th
ruleNUM_MUL _ _ _ _ = fail "ruleNUM_MUL"
              
convNUM_SHIFT :: WFCtxt thry => Int -> Conversion cls thry
convNUM_SHIFT 0 = Conv $ \ tm -> primINST [(tmN, tm)] convNUM_SHIFT_pth_base 
  where convNUM_SHIFT_pth_base :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth_base = cacheProof "convNUM_SHIFT_pth_base" ctxtWF .
            prove [txt| n = _0 + BIT1 _0 * n |] $
              tacMESON [thmADD_CLAUSES, thmMULT_CLAUSES, defNUMERAL]
convNUM_SHIFT k = Conv $ \ tm -> note "convNUM_SHIFT" $
    case tm of 
      (Comb _ (Comb _ (Comb _ (Comb _ _))))
          | k >= 4 ->
              do (i, ntm) <- topsplit tm
                 th1 <- runConv (convNUM_SHIFT (k - 4)) ntm
                 case concl th1 of
                   (Comb _ (Comb (Comb _ ZERO)(Comb (Comb _ ptm) btm))) ->
                     do pths <- convNUM_SHIFT_pths0
                        let th2 = pths !! i
                        th3 <- primINST [(tmN, ntm), (tmB, btm), (tmP, ptm)] th2
                        primEQ_MP th3 th1
                   (Comb _ (Comb (Comb _ atm) (Comb (Comb _ ptm) btm))) ->
                     do pths <- convNUM_SHIFT_pths1
                        let th2 = pths !! i
                        th3 <- primINST [ (tmN, ntm), (tmA, atm)
                                        , (tmB, btm), (tmP, ptm) ] th2
                        primEQ_MP th3 th1
                   _ -> fail "malformed numeral for k >= 4."
          | otherwise -> fail "malformed numeral for k < 4."
      (BIT0 ntm) ->
          do th1 <- runConv (convNUM_SHIFT (k - 1)) ntm
             case concl th1 of
               (Comb _ (Comb (Comb _ ZERO) (Comb (Comb _ ptm) btm))) ->
                 primEQ_MP (primINST [ (tmN, ntm), (tmB, btm)
                                     , (tmP, ptm) ] convNUM_SHIFT_pthz) th1
               (Comb _ (Comb (Comb _ atm) (Comb (Comb _ ptm) btm))) ->
                 primEQ_MP (primINST [ (tmN, ntm), (tmA, atm)
                                     , (tmB, btm), (tmP, ptm) 
                                     ] convNUM_SHIFT_pth0) th1 
               _ -> fail "bad BIT0 case."
      (BIT1 ntm) ->
          do th1 <- runConv (convNUM_SHIFT (k - 1)) ntm
             let (Comb _ (Comb (Comb _ atm)
                          (Comb (Comb _ ptm) btm))) = concl th1
             th2 <- primINST [ (tmN, ntm), (tmA, atm)
                             , (tmB, btm), (tmP, ptm) ] convNUM_SHIFT_pth1
             primEQ_MP th2 th1 
      ZERO ->
          do th1 <- runConv (convNUM_SHIFT (k - 1)) tm
             let (Comb _ (Comb (Comb _ atm)
                          (Comb (Comb _ ptm) btm))) = concl th1
             th2 <- primINST [ (tmA, atm), (tmB, btm)
                             , (tmP, ptm) ] convNUM_SHIFT_pth_triv
             primEQ_MP th2 th1 
      _ -> fail "malformed numeral."
  where convNUM_SHIFT_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth0 = cacheProof "convNUM_SHIFT_pth0" ctxtWF .
            prove [txt| (n = a + p * b <=> BIT0 n = BIT0 a + BIT0 p * b) |] $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_SHIFT_pthz :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pthz = cacheProof "convNUM_SHIFT_pthz" ctxtWF $
            do th1 <- ruleSPEC [txt| _0 |] defNUMERAL
               prove [txt| n = _0 + p * b <=> BIT0 n = _0 + BIT0 p * b |] $
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN`
                 tacREWRITE [thmADD_CLAUSES, ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [ ruleGSYM thmMULT_ASSOC, thmEQ_MULT_LCANCEL
                            , thmARITH_EQ ]

        convNUM_SHIFT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth1 = cacheProof "convNUM_SHIFT_pth1" ctxtWF .
            prove [txt| (n = a + p * b <=> BIT1 n = BIT1 a + BIT0 p * b) |] $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB, thmADD_CLAUSES
                         , thmSUC_INJ ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_SHIFT_pth_triv :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_SHIFT_pth_triv = cacheProof "convNUM_SHIFT_pth_triv" ctxtWF $
            do th1 <- ruleSPEC [txt| _0 |] defNUMERAL
               prove [txt| _0 = a + p * b <=> _0 = a + BIT0 p * b |] $
                 tacCONV (convBINOP convSYM) `_THEN`
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmADD_EQ_0, thmMULT_EQ_0, thmBIT0]
                      
convNUM_UNSHIFT :: WFCtxt thry => Conversion cls thry
convNUM_UNSHIFT = Conv $ \ tm -> note "convNUM_UNSHIFT" $
    case tm of
      (atm :+ (ptm :* btm)) ->
          case (atm, ptm, btm) of
            (_, _, ZERO) ->
                primINST [(tmA, atm), (tmP, ptm)] convNUM_UNSHIFT_pth_triv
            (_, BIT1 ZERO, _) ->
                do th1 <- primINST [ (tmA, atm)
                                   , (tmB, btm) ] convNUM_UNSHIFT_pth_base
                   let (Comb _ (Comb (Comb _ mtm) ntm)) = concl th1
                   th2 <- ruleNUM_ADD mtm ntm
                   primTRANS th1 th2
            (Comb _ (Comb _ (Comb _ (Comb _ atm'))),
             Comb _ (Comb _ (Comb _ (Comb _ ptm'@(Comb _ _)))), _) ->
                do (i, _) <- topsplit atm
                   case (atm', ptm') of
                     (Comb _ (Comb _ (Comb _ (Comb _ atm''))),
                      Comb _ (Comb _ (Comb _ (Comb _ ptm''@(Comb _ _))))) ->
                         do (j, _) <- topsplit atm'
                            tm' <- mkComb (mkComb tmAdd atm'')
                                     (mkComb (mkComb tmMul ptm'') btm)
                            th1 <- runConv convNUM_UNSHIFT tm'
                            pths <- convNUM_UNSHIFT_puths2
                            let pth = pths !! (16 * j + i)
                            ntm <- rand $ concl th1
                            th2 <- primINST [ (tmA, atm''), (tmP, ptm'')
                                            , (tmB, btm), (tmN, ntm) ] pth
                            primEQ_MP th2 th1
                     _ -> 
                        do tm' <- mkComb (mkComb tmAdd atm')
                                    (mkComb (mkComb tmMul ptm') btm)
                           th1 <- runConv convNUM_UNSHIFT tm'
                           pths <- convNUM_UNSHIFT_puths1
                           let pth = pths !! i
                           ntm <- rand $ concl th1
                           th2 <- primINST [ (tmA, atm'), (tmP, ptm')
                                           , (tmB, btm), (tmN, ntm) ] pth
                           primEQ_MP th2 th1
            (ZERO, BIT0 qtm, _) ->
                do th1 <- primINST [ (tmB, btm)
                                   , (tmP, qtm) ] convNUM_UNSHIFT_pthz
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            (BIT0 ctm, BIT0 qtm, _) ->
                do th1 <- primINST [ (tmA, ctm), (tmB, btm)
                                   , (tmP, qtm) ] convNUM_UNSHIFT_pth0
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            (BIT1 ctm, BIT0 qtm, _) ->
                do th1 <- primINST [ (tmA, ctm), (tmB, btm)
                                   , (tmP, qtm) ] convNUM_UNSHIFT_pth1
                   ruleCONV (convRAND (convRAND convNUM_UNSHIFT)) th1
            _ -> fail "malformed numeral"
      _ -> fail "malformed numeral"
  where convNUM_UNSHIFT_pth_triv :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth_triv = 
            cacheProof "convNUM_UNSHIFT_pth_triv" ctxtWF $
              do th1 <- ruleSPEC [txt| _0 |] defNUMERAL
                 prove [txt| a + p * _0 = a |] $
                   tacSUBST1 (ruleSYM th1) `_THEN` 
                   tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES]

        convNUM_UNSHIFT_pth_base :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth_base = 
            cacheProof "convNUM_UNSHIFT_pth_base" ctxtWF $
              do th1 <- ruleSPEC [txt| BIT1 _0 |] defNUMERAL
                 prove [txt| a + BIT1 _0 * b = a + b |] $
                   tacSUBST1 (ruleSYM th1) `_THEN`
                   tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES]

        convNUM_UNSHIFT_pth0 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth0 = cacheProof "convNUM_UNSHIFT_pth0" ctxtWF .
            prove [txt| BIT0 a + BIT0 p * b = BIT0(a + p * b) |] $
              tacREWRITE [thmBIT0] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [ruleGSYM thmMULT_ASSOC, ruleGSYM thmLEFT_ADD_DISTRIB]

        convNUM_UNSHIFT_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pth1 = cacheProof "convNUM_UNSHIFT_pth1" ctxtWF .
            prove [txt| BIT1 a + BIT0 p * b = BIT1(a + p * b) |] $
              tacREWRITE [thmBIT0, thmBIT1] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [thmADD_CLAUSES, thmSUC_INJ] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        convNUM_UNSHIFT_pthz :: WFCtxt thry => HOL cls thry HOLThm
        convNUM_UNSHIFT_pthz = cacheProof "convNUM_UNSHIFT_pthz" ctxtWF $
            do th1 <- ruleSPEC [txt| _0 |] defNUMERAL
               prove [txt| _0 + BIT0 p * b = BIT0(_0 + p * b) |] $
                 tacSUBST1 (ruleSYM th1) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN` 
                 tacREWRITE [thmADD_CLAUSES] `_THEN`
                 tacREWRITE [thmRIGHT_ADD_DISTRIB]

ruleNUM_SQUARE :: WFCtxt thry => HOLTerm -> HOL cls thry HOLThm
ruleNUM_SQUARE tm = note "ruleNUM_SQUARE" $
    do (w, z) <- bitcounts tm
       ruleGEN_NUM_SQUARE w z tm
  where ruleGEN_NUM_SQUARE :: WFCtxt thry => Int -> Int 
                           -> HOLTerm -> HOL cls thry HOLThm
        ruleGEN_NUM_SQUARE _ _ ZERO = ruleNUM_SQUARE_pth0
        ruleGEN_NUM_SQUARE w z (BIT0 (BIT0 (BIT0 ptm))) =
            do th1 <- ruleGEN_NUM_SQUARE w (z - 3) ptm
               ntm <- rand $ concl th1
               th2 <- primINST [(tmM, ptm), (tmN, ntm)] ruleNUM_SQUARE_pth_even3
               primEQ_MP th2 th1
        ruleGEN_NUM_SQUARE w z (BIT0 mtm) =
            do th1 <- ruleGEN_NUM_SQUARE w (z - 1) mtm
               ntm <- rand $ concl th1
               th2 <- primINST [(tmM, mtm), (tmN, ntm)] ruleNUM_SQUARE_pth_even
               primEQ_MP th2 th1
        ruleGEN_NUM_SQUARE _ _ (BIT1 ZERO) = ruleNUM_SQUARE_pth1
        ruleGEN_NUM_SQUARE w z (BIT1 mtm)
            | (w < 100 || z < 20) && w + z < 150 =
                case mtm of
                  (BIT1 (BIT1 ntm)) ->
                      do tmOne <- serve [wf| BIT1 _0 |]
                         th1 <- ruleNUM_ADD ntm tmOne
                         mtm' <- rand $ concl th1
                         th2 <- ruleNUM_SQUARE mtm'
                         ptm <- rand $ concl th2
                         ptm' <- mkComb tmBIT0 $ mkComb tmBIT0 ptm
                         atm <- subbn ptm' mtm'
                         th3 <- ruleNUM_ADD mtm' atm
                         th4 <- primINST [ (tmA, atm), (tmM, mtm'), (tmN, ntm)
                                         , (tmP, ptm) ] ruleNUM_SQUARE_pth_qstep
                         th5 <- ruleCONJ th1 $ ruleCONJ th2 th3
                         ruleQUICK_PROVE_HYP th5 th4
                  _ ->
                      do th1 <- ruleGEN_NUM_SQUARE (w - 1) z mtm
                         ntm <- rand $ concl th1
                         pth' <- primINST [ (tmM, mtm)
                                          , (tmN, ntm) ] ruleNUM_SQUARE_pth_odd
                         th2 <- primEQ_MP pth' th1
                         let (Comb _ 
                              (Comb _ 
                               (Comb _ (Comb (Comb _ ptm) qtm)))) = concl th2
                         th3 <- ruleNUM_ADD ptm qtm
                         th4 <- ruleAP_BIT1 $ ruleAP_BIT0 th3
                         primTRANS th2 th4
            | w + z < 800 =
               let k2 = (w + z) `div` 2 in
                 do th1 <- runConv (convNUM_SHIFT k2) tm
                    (Comb (Comb _ ltm) 
                     (Comb (Comb _ ptm) htm)) <- rand $ concl th1
                    th2 <- ruleNUM_ADD htm ltm
                    mtm' <- rand $ concl th2
                    th3 <- ruleNUM_SQUARE htm
                    th4 <- ruleNUM_SQUARE ltm
                    th5 <- ruleNUM_SQUARE mtm'
                    atm <- rand $ concl th3
                    ctm <- rand $ concl th4
                    dtm <- rand $ concl th5
                    th6 <- ruleNUM_ADD atm ctm
                    etm <- rand $ concl th6
                    btm <- subbn dtm etm
                    th7 <- ruleNUM_ADD etm btm
                    dtm' <- rand $ concl th7
                    th8 <- primINST [ (tmA, atm), (tmB, btm), (tmC, ctm)
                                    , (tmD, dtm'), (tmE, etm), (tmH, htm)
                                    , (tmL, tm), (tmM, mtm'), (tmN, tm)
                                    , (tmP, ptm)] ruleNUM_SQUARE_pth_rec
                    th9 <- foldr1M ruleCONJ [th1, th2, th3, th4, th5, th6, th7]
                    th10 <- ruleQUICK_PROVE_HYP th9 th8
                    ruleCONV (convRAND (convRAND 
                                        (convRAND convNUM_UNSHIFT) `_THEN` 
                                        convNUM_UNSHIFT)) th10
            | otherwise =
                let k3 = (w + z) `div` 3 in
                  do th0 <- runConv (convNUM_SHIFT k3 `_THEN`
                                     convRAND (convRAND (convNUM_SHIFT k3))) tm
                     (Comb (Comb _ ltm) 
                      (Comb (Comb _ ptm)
                       (Comb (Comb _ mtm') 
                        (Comb (Comb _ _) htm)))) <- rand $ concl th0
                     th1 <- ruleNUM_SQUARE htm
                     th2 <- ruleNUM_SQUARE ltm
                     atm <- rand $ concl th2
                     etm <- rand $ concl th1
                     lnum <- destRawNumeral ltm
                     mnum <- destRawNumeral mtm'
                     hnum <- destRawNumeral htm
                     b <- mkNumeral $ 2 * lnum * mnum
                     btm <- rand b
                     c <- mkNumeral $ mnum * mnum + 2 * lnum * hnum
                     ctm <- rand c
                     d <- mkNumeral $ 2 * hnum * mnum
                     dtm <- rand d
                     th <- primINST [ (tmA, atm), (tmB, btm), (tmC, ctm)
                                    , (tmD, dtm), (tmE, etm), (tmH, htm)
                                    , (tmM, mtm'), (tmL, ltm)
                                    , (tmP, ptm) ] ruleNUM_SQUARE_pth_toom3
                     th' <- ruleCONV (convBINOP2 (convRAND (convRAND 
                                      (convBINOP2 convTOOM3 
                                       (convBINOP2 convTOOM3 convTOOM3)))) 
                                      convTOOM3) th
                     [tm3, tm4, tm5] <- liftM conjuncts $ rand =<< 
                                          rand =<< lHand (concl th')
                     th3 <- ruleNUM_SQUARE =<< lHand =<< lHand tm3
                     th4 <- ruleNUM_SQUARE =<< lHand =<< lHand tm4
                     th5 <- ruleNUM_SQUARE =<< lHand =<< lHand tm5
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
            prove [txt| _0 EXP 2 = _0 |] $
              tacMESON [ defNUMERAL
                       , runConv (convREWRITE [thmARITH]) [txt| 0 EXP 2 |] ]

        ruleNUM_SQUARE_pth1 :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth1 = cacheProof "ruleNUM_SQUARE_pth1" ctxtWF .
            prove [txt| (BIT1 _0) EXP 2 = BIT1 _0 |] $
              tacMESON [ defNUMERAL
                       , runConv (convREWRITE [thmARITH]) [txt| 1 EXP 2 |] ]

        ruleNUM_SQUARE_pth_even :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_even = cacheProof "ruleNUM_SQUARE_pth_even" ctxtWF .
            prove [txt| m EXP 2 = n <=> (BIT0 m) EXP 2 = BIT0(BIT0 n) |] $
              tacABBREV [txt| two = 2 |] `_THEN`
              tacREWRITE [thmBIT0] `_THEN` tacEXPAND [txt| two |] `_THEN`
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN` 
              tacREWRITE [thmEXP_2] `_THEN`
              tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                            [txt| (2 * m) * (2 * n) = 2 * 2 * m * n |]
                         ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

        ruleNUM_SQUARE_pth_odd :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_odd = cacheProof "ruleNUM_SQUARE_pth_odd" ctxtWF .
            prove [txt| m EXP 2 = n <=> (BIT1 m) EXP 2 = BIT1(BIT0(m + n)) |] $
              tacABBREV [txt| two = 2 |] `_THEN`
              tacREWRITE [defNUMERAL, thmBIT0, thmBIT1] `_THEN`
              tacEXPAND [txt| two |] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacREWRITE [thmEXP_2, thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
              tacREWRITE [ thmSUC_INJ, ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [runConv (convAC thmADD_AC) =<< toHTm
                            [txt| (m + m * 2 * m) + m = m * 2 * m + m + m |]
                         ] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_2
                         , runConv (convAC thmMULT_AC) =<< toHTm
                             [txt| m * 2 * m = 2 * m * m |]
                         ] `_THEN`
              tacREWRITE [ ruleGSYM thmMULT_ASSOC
                         , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ] `_THEN`
              tacGEN_REWRITE (convRAND . convRAND) [thmADD_SYM] `_THEN`
              tacREWRITE [thmEQ_ADD_RCANCEL]

        ruleNUM_SQUARE_pth_qstep :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_qstep = 
          cacheProof "ruleNUM_SQUARE_pth_qstep" ctxtWF $
            ruleUNDISCH =<< 
              prove [txt| n + BIT1 _0 = m /\
                          m EXP 2 = p /\
                          m + a = BIT0(BIT0 p)
                          ==> (BIT1(BIT1(BIT1 n))) EXP 2 = 
                               BIT1(BIT0(BIT0(BIT0 a))) |]
                (tacABBREV [txt| two = 2 |] `_THEN`
                 tacSUBST1 (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN` 
                 tacEXPAND [txt| two |] `_THEN`
                 tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [ thmADD1, thmLEFT_ADD_DISTRIB
                            , ruleGSYM thmADD_ASSOC ] `_THEN`
                 tacREWRITE [thmMULT_ASSOC] `_THEN` 
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [thmIMP_CONJ] `_THEN`
                 _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
                 _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN` tacDISCH `_THEN`
                 tacMATCH_MP (ruleMESON [thmEQ_ADD_LCANCEL] 
                               [txt| !m:num. m + n = m + p ==> n = p |]) `_THEN`
                 tacEXISTS [txt| 16 * (n + 1) |] `_THEN`
                 tacASM_REWRITE [ thmADD_ASSOC
                                , ruleGSYM thmLEFT_ADD_DISTRIB ] `_THEN`
                 tacEXPAND [txt| two |] `_THEN` 
                 tacREWRITE [thmEXP_2] `_THEN`
                 tacREWRITE [thmLEFT_ADD_DISTRIB, thmRIGHT_ADD_DISTRIB] `_THEN`
                 tacREWRITE [thmMULT_CLAUSES, thmMULT_ASSOC] `_THEN`
                 tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                             [txt| (8 * n) * NUMERAL p = (8 * NUMERAL p) * n |]
                            ] `_THEN`
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [runConv (convAC thmADD_AC) =<< toHTm
                               [txt| (n + 16) + p + q + 49 = 
                                     (n + p + q) + (16 + 49) |]
                            ] `_THEN`
                 tacREWRITE [ruleGSYM thmADD_ASSOC] `_THEN` 
                 tacREWRITE [thmARITH] `_THEN`
                 tacREWRITE [thmADD_ASSOC, thmEQ_ADD_RCANCEL] `_THEN`
                 tacREWRITE [ ruleGSYM thmADD_ASSOC, ruleGSYM thmMULT_2
                            , thmMULT_ASSOC] `_THEN`
                 tacONCE_REWRITE [runConv (convAC thmADD_AC) =<< toHTm
                                    [txt| a + b + c:num = b + a + c |]
                                 ] `_THEN`
                 tacREWRITE [ruleGSYM thmRIGHT_ADD_DISTRIB] `_THEN`
                 tacREWRITE [thmARITH])

        ruleNUM_SQUARE_pth_rec :: WFCtxt thry => HOL cls thry HOLThm
        ruleNUM_SQUARE_pth_rec = cacheProof "ruleNUM_SQUARE_pth_rec" ctxtWF $
            ruleUNDISCH =<< 
              prove [txt| n = l + p * h /\
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
        ruleNUM_SQUARE_pth_toom3 = 
          cacheProof "ruleNUM_SQUARE_pth_toom3" ctxtWF $
            do rewrites <- mapM (\ k -> 
                             do n <- mkSmallNumeral (k - 1)
                                th <- runConv (convREWRITE [thmARITH_SUC]) $ 
                                        mkComb tmSuc n
                                ruleSYM th) [1..5]
               prove [txt| h EXP 2 = e /\
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
                 tacABBREV [txt| two = 2 |] `_THEN`
                 tacSUBST1 (ruleMESON [defNUMERAL] [txt| _0 = 0 |]) `_THEN`
                 tacREWRITE [thmBIT1, thmBIT0] `_THEN`
                 tacEXPAND [txt| two |] `_THEN` 
                 tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
                 tacREWRITE [thmARITH] `_THEN`
                 _SUBGOAL_THEN 
                   [txt| !p x y z. (x + p * (y + p * z)) EXP 2 =
                           x * x + p * (2 * x * y + p * ((2 * x * z + y * y) +
                             p * (2 * y * z + p * z * z))) |]
                 (\ th -> tacREWRITE [th]) `_THENL`
                 [ tacREWRITE [ thmEXP_2, thmMULT_2, thmLEFT_ADD_DISTRIB
                              , thmRIGHT_ADD_DISTRIB ] `_THEN`
                   tacREWRITE [thmMULT_AC] `_THEN` tacREWRITE [thmADD_AC]
                 , tacREWRITE [thmEXP_2]
                 ] `_THEN`
                _MAP_EVERY tacABBREV
                  [ [txt| a':num = l * l", "b' = 2 * l * m |]
                  , [txt| c' = 2 * l * h + m * m |]
                  , [txt| d' = 2 * m * h", "e':num = h * h |] 
                  ] `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             [txt| 2 * m * l = 2 * l * m |]) `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             [txt| 2 * h * l = 2 * l * h |]) `_THEN`
                tacSUBST1 (runConv (convAC thmMULT_AC) =<< toHTm 
                             [txt| 2 * h * m = 2 * m * h |]) `_THEN`
                tacASM_REWRITE_NIL `_THEN` tacEXPAND [txt| two |] `_THEN`
                _POP_ASSUM_LIST (const _ALL) `_THEN`
                tacASM_CASES [txt| a':num = a |] `_THEN` 
                tacASM_REWRITE_NIL `_THEN`
                tacASM_CASES [txt| e':num = e |] `_THEN` 
                tacASM_REWRITE_NIL `_THEN`
                _POP_ASSUM_LIST (const _ALL) `_THEN`
                tacREWRITE [thmEQ_ADD_LCANCEL, thmEQ_MULT_LCANCEL] `_THEN`
                tacREWRITE [thmLEFT_ADD_DISTRIB, thmMULT_ASSOC] `_THEN`
                tacREWRITE [thmARITH] `_THEN`
                tacREWRITE [thmMULT_CLAUSES, thmEQ_ADD_LCANCEL] `_THEN`
                tacREWRITE [thmADD_ASSOC, thmEQ_ADD_RCANCEL] `_THEN`
                tacREWRITE [ruleGSYM thmADD_ASSOC] `_THEN` tacDISCH `_THEN`
                _FIRST_ASSUM (tacMP . ruleMATCH_MP 
                              (ruleMESON_NIL [txt| b = b' /\ c = c' /\ d = d' 
                                                   ==> 5 * b + c' + d' = 
                                                   5 * b' + c + d |])) `_THEN`
                tacREWRITE [thmLEFT_ADD_DISTRIB, thmMULT_ASSOC] `_THEN`
                tacREWRITE rewrites `_THEN`
                tacREWRITE [thmMULT_CLAUSES, thmADD_CLAUSES] `_THEN`
                tacCONV (convLAND convNUM_CANCEL) `_THEN` 
                _DISCH_THEN tacSUBST_ALL `_THEN`
                _FIRST_ASSUM (tacMP . ruleMATCH_MP 
                              (ruleMESON_NIL 
                                 [txt| b = b' /\ c = c' /\ d = d' ==>
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
        ruleNUM_SQUARE_pth_even3 = 
          cacheProof "ruleNUM_SQUARE_pth_even3" ctxtWF .
            prove [txt| m EXP 2 = n <=>
                       (BIT0(BIT0(BIT0 m))) EXP 2 = 
                        BIT0(BIT0(BIT0(BIT0(BIT0(BIT0 n))))) |] $
              tacABBREV [txt| two = 2 |] `_THEN`
              tacREWRITE [thmBIT0] `_THEN` 
              tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
              tacEXPAND [txt| two |] `_THEN` tacREWRITE [thmEXP_2] `_THEN`
              tacREWRITE [runConv (convAC thmMULT_AC) =<< toHTm
                          [txt| (2 * 2 * 2 * m) * 2 * 2 * 2 * m = 
                                  2 * 2 * 2 * 2 * 2 * 2 * m * m |]] `_THEN`
              tacREWRITE [thmEQ_MULT_LCANCEL, thmARITH_EQ]

convNUM_GT :: WFCtxt thry => Conversion cls thry
convNUM_GT = convGEN_REWRITE id [defGT] `_THEN` convNUM_LT

convNUM_GE :: WFCtxt thry => Conversion cls thry
convNUM_GE = convGEN_REWRITE id [defGE] `_THEN` convNUM_LE

convNUM_PRE :: WFCtxt thry => Conversion cls thry
convNUM_PRE = Conv $ \ tm ->
    case tm of
      Comb (Const "PRE" _) r ->
          do x <- destNumeral r
             if x == 0 then tth
                else do tm' <- mkNumeral $ pred x
                        th1 <- runConv convNUM_SUC $ mkComb [wf|SUC|] tm'
                        th2 <- primINST [ ([wf|m:num|], tm'), ([wf|n:num|], r)
                                        ] pth
                        ruleMP th2 th1
      _ -> fail "convNUM_PRE"
  where tth :: WFCtxt thry => HOL cls thry HOLThm
        tth = cacheProof "convNUM_PRE_tth" ctxtWF .
            prove [txt| PRE 0 = 0 |] $ tacREWRITE [defPRE]

        pth :: WFCtxt thry => HOL cls thry HOLThm
        pth = cacheProof "convNUM_PRE_pth" ctxtWF .
            prove [txt| (SUC m = n) ==> (PRE n = m) |] $
              _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN` tacREWRITE [defPRE]

convNUM_SUB :: WFCtxt thry => Conversion cls thry
convNUM_SUB = Conv $ \ tm -> note "convNUM_SUB" $
    do (l, r) <- destBinop [wf|(-)|] tm
       ln <- destNumeral l
       rn <- destNumeral r
       if ln <= rn
          then do pth <- primINST [([wf|p:num|], l), ([wf|n:num|], r)] pth0
                  th0 <- ruleEQT_ELIM . runConv convNUM_LE $ 
                           mkBinop [wf|(<=)|] l r
                  ruleMP pth th0
          else do k <- mkNumeral (ln - rn)
                  pth <- primINST [ ([wf|m:num|], k), ([wf|p:num|], l)
                                  , ([wf|n:num|], r) ] pth1
                  th0 <- runConv convNUM_ADD $ mkBinop [wf|(+)|] k r
                  ruleMP pth th0
  where pth0 :: WFCtxt thry => HOL cls thry HOLThm
        pth0 = cacheProof "convNUM_SUB_pth0" ctxtWF .
            prove [txt| p <= n ==> (p - n = 0) |] $ tacREWRITE [thmSUB_EQ_0]

        pth1 :: WFCtxt thry => HOL cls thry HOLThm
        pth1 = cacheProof "convNUM_SUB_pth1" ctxtWF .
            prove [txt| (m + n = p) ==> (p - n = m) |] $ 
              _DISCH_THEN (tacSUBST1 . ruleSYM) `_THEN`
              tacREWRITE [thmADD_SUB]


convNUM_DIVMOD :: WFCtxt thry => Integer -> Integer -> HOL cls thry HOLThm
convNUM_DIVMOD x y =
    let (k, l) = x `quotRem` y in
      do th0 <- primINST [([wf|m:num|], mkNumeral x), ([wf|n:num|], mkNumeral y)
                         ,([wf|q:num|], mkNumeral k), ([wf|r:num|], mkNumeral l)
                         ] pth
         tm0 <- lHand . lHand $ concl th0
         th1 <- runConv (convLAND convNUM_MULT `_THEN` convNUM_ADD) tm0
         th2 <- ruleMP th0 th1
         tm2 <- lHand $ concl th2
         ruleMP th2 . ruleEQT_ELIM $ runConv convNUM_LT tm2
  where pth :: WFCtxt thry => HOL cls thry HOLThm
        pth = cacheProof "convNUM_DIVMOD_pth" ctxtWF .
            prove [txt| (q * n + r = m) ==> r < n ==> 
                        (m DIV n = q) /\ (m MOD n = r) |] $
              tacMESON [thmDIVMOD_UNIQ]


convNUM_DIV :: WFCtxt thry => Conversion cls thry
convNUM_DIV = Conv $ \ tm ->
    case tm of
      Binary "DIV" xt yt ->
          do xt' <- destNumeral xt
             yt' <- destNumeral yt
             ruleCONJUNCT1 $ convNUM_DIVMOD xt' yt'
      _ -> fail' "convNUM_DIV"

convNUM_MOD :: WFCtxt thry => Conversion cls thry
convNUM_MOD = Conv $ \ tm ->
    case tm of
      Binary "MOD" xt yt ->
          do xt' <- destNumeral xt
             yt' <- destNumeral yt
             ruleCONJUNCT2 $ convNUM_DIVMOD xt' yt'
      _ -> fail' "convNUM_MOD"

convNUM_FACT :: WFCtxt thry => Conversion cls thry
convNUM_FACT = Conv $ \ tm ->
    case tm of
      Comb (Const "FACT" _) r -> convNUM_FACT' =<< destNumeral r
      _ -> fail' "convNUM_FACT"
  where convNUM_FACT' :: WFCtxt thry => Integer -> HOL cls thry HOLThm
        convNUM_FACT' 0 = pth0
        convNUM_FACT' n =
            do th0 <- mksuc n
               tmx <- rand . lHand $ concl th0
               tm0 <- rand $ concl th0
               th1 <- convNUM_FACT' $ pred n
               tm1 <- rand $ concl th1
               th2 <- runConv convNUM_FACT $ mkBinop [wf| (*) |] tm0 tm1
               tm2 <- rand $ concl th2
               pth <- primINST [ ([wf|x:num|], tmx), ([wf|y:num|], tm0)
                               , ([wf|w:num|], tm1), ([wf|z:num|], tm2)
                               ] pthSuc
               ruleMP (ruleMP (ruleMP pth th0) th1) th2

        mksuc :: WFCtxt thry => Integer -> HOL cls thry HOLThm
        mksuc = runConv convNUM_SUC . mkComb [wf|SUC|] . mkNumeral . pred

        pth0 :: WFCtxt thry => HOL cls thry HOLThm
        pth0 = cacheProof "convNUM_FACT_pth0" ctxtWF .
            prove [txt| FACT 0 = 1 |] $ tacREWRITE [defFACT]

        pthSuc :: WFCtxt thry => HOL cls thry HOLThm
        pthSuc = cacheProof "convNUM_FACT_pthSuc" ctxtWF .
            prove [txt| (SUC x = y) ==> (FACT x = w) ==> 
                        (y * w = z) ==> (FACT y = z) |] $
              _REPEAT (_DISCH_THEN (tacSUBST1 . ruleSYM)) `_THEN`
              tacREWRITE [defFACT]

convNUM_MAX :: WFCtxt thry => Conversion cls thry
convNUM_MAX =
  convREWR defMAX `_THEN` convRATOR (convRATOR (convRAND convNUM_LE)) `_THEN`
  convGEN_REWRITE id [thmCOND_CLAUSES]

convNUM_MIN :: WFCtxt thry => Conversion cls thry
convNUM_MIN =
  convREWR defMIN `_THEN` convRATOR (convRATOR (convRAND convNUM_LE)) `_THEN`
  convGEN_REWRITE id [thmCOND_CLAUSES]

convNUM :: WFCtxt thry => Conversion cls thry
convNUM = Conv $ \ tm -> note "convNUM" $
    do n <- liftM ((+) (-1)) $ destNumeral tm
       if n < 0
          then fail "negative number."
          else do tm' <- mkNumeral n
                  th <- runConv convNUM_SUC $ mkComb tmSUC tm'
                  ruleSYM th

convNUM_RED :: WFCtxt thry => Conversion cls thry
convNUM_RED = Conv $ \ tm ->
  do net <- basicNet
     net' <- liftM (foldr (uncurry netOfConv) net) $
               mapM (toHTm `ffCombM` return)
                 [ ([wf| SUC(NUMERAL n) |], 
                    HINT "convNUM_SUC" "HaskHOL.Lib.CalcNum")
                 , ([wf| PRE(NUMERAL n) |], 
                    HINT "convNUM_PRE" "HaskHOL.Lib.CalcNum")
                 , ([wf| FACT(NUMERAL n) |], 
                    HINT "convNUM_FACT" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m < NUMERAL n |], 
                    HINT "convNUM_LT" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m <= NUMERAL n |], 
                    HINT "convNUM_LE" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m > NUMERAL n |], 
                    HINT "convNUM_GT" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m >= NUMERAL n |], 
                    HINT "convNUM_GE" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m = NUMERAL n |], 
                    HINT "convNUM_EQ" "HaskHOL.Lib.CalcNum")
                 , ([wf| EVEN(NUMERAL n) |], 
                    HINT "convNUM_EVEN" "HaskHOL.Lib.CalcNum")
                 , ([wf| ODD(NUMERAL n) |], 
                    HINT "convNUM_ODD" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m + NUMERAL n |], 
                    HINT "convNUM_ADD" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m - NUMERAL n |], 
                    HINT "convNUM_SUB" "HaskHOL.Lib.CalcNum")
                 , ([wf| NUMERAL m * NUMERAL n |], 
                    HINT "convNUM_MULT" "HaskHOL.Lib.CalcNum")
                 , ([wf| (NUMERAL m) EXP (NUMERAL n) |], 
                    HINT "convNUM_EXP" "HaskHOL.Lib.CalcNum")
                 , ([wf| (NUMERAL m) DIV (NUMERAL n) |], 
                    HINT "convNUM_DIV" "HaskHOL.Lib.CalcNum")
                 , ([wf| (NUMERAL m) MOD (NUMERAL n) |], 
                    HINT "convNUM_MOD" "HaskHOL.Lib.CalcNum")
                 , ([wf| MAX (NUMERAL m) (NUMERAL n) |], 
                    HINT "convNUM_MAX" "HaskHOL.Lib.CalcNum")
                 , ([wf| MIN (NUMERAL m) (NUMERAL n) |], 
                    HINT "convNUM_MIN" "HaskHOL.Lib.CalcNum")
                 ]
     runConv (gconvREWRITES net') tm

convNUM_REDUCE :: WFCtxt thry => Conversion cls thry
convNUM_REDUCE = convDEPTH convNUM_RED

-- Misc utility stuff
ruleAP_BIT0 :: (WFCtxt thry, HOLThmRep thm cls thry) 
            => thm -> HOL cls thry HOLThm
ruleAP_BIT0 th = primMK_COMB (primREFL tmBIT0) th

ruleAP_BIT1 :: (WFCtxt thry, HOLThmRep thm cls thry) 
            => thm -> HOL cls thry HOLThm
ruleAP_BIT1 th = primMK_COMB (primREFL tmBIT1) th

ruleQUICK_PROVE_HYP :: HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleQUICK_PROVE_HYP ath bth =
    primEQ_MP (primDEDUCT_ANTISYM ath bth) ath

destRawNumeral :: MonadThrow m => HOLTerm -> m Int
destRawNumeral (BIT1 t) =
    do t' <- destRawNumeral t
       return $! 2 * t' + 1
destRawNumeral (BIT0 t) =
    do t' <- destRawNumeral t
       return $! 2 * t'
destRawNumeral ZERO = return 0
destRawNumeral _ = fail' "destRawNumeral"

bitcounts :: MonadThrow m => HOLTerm -> m (Int, Int)
bitcounts = bctr 0 0
  where bctr :: MonadThrow m => Int -> Int -> HOLTerm -> m (Int, Int)
        bctr w z ZERO = return (w, z)
        bctr w z (BIT0 t) = bctr w (succ z) t
        bctr w z (BIT1 t) = bctr (succ w) z t
        bctr _ _ _ = fail' "bitcounts"

wellformed :: HOLTerm -> Bool
wellformed ZERO = True
wellformed (BIT0 t) = wellformed t
wellformed (BIT1 t) = wellformed t
wellformed _ = False

orderrelation :: HOLTerm -> HOLTerm -> Maybe Ordering
orderrelation mtm ntm
    | mtm == ntm = if wellformed mtm then Just EQ else Nothing
    | otherwise =
        case (mtm, ntm) of
          (ZERO, ZERO) -> Just EQ
          (ZERO, _) ->
              if wellformed ntm then Just LT else Nothing
          (_, ZERO) ->
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
doublebn tm@ZERO = return tm
doublebn tm = mkComb tmBIT0 tm

subbn :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
subbn = subbnRec
  where subbnRec :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
        subbnRec mtm ZERO = return mtm
        subbnRec (BIT0 mt) (BIT0 nt) = doublebn =<< subbnRec mt nt
        subbnRec (BIT1 mt) (BIT1 nt) = doublebn =<< subbnRec mt nt
        subbnRec (BIT1 mt) (BIT0 nt) = mkComb tmBIT1 $ subbnRec mt nt
        subbnRec (BIT0 mt) (BIT1 nt) = mkComb tmBIT1 $ sbcbn mt nt
        subbnRec _ _ = fail "subbn"

sbcbn :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
sbcbn = sbcbnRec
  where sbcbnRec :: WFCtxt thry => HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
        sbcbnRec (BIT0 mt) nt@ZERO = mkComb tmBIT1 $ sbcbnRec mt nt
        sbcbnRec (BIT1 mt) ZERO = doublebn mt
        sbcbnRec (BIT0 mt) (BIT0 nt) = mkComb tmBIT1 $ sbcbnRec mt nt
        sbcbnRec (BIT1 mt) (BIT1 nt) = mkComb tmBIT1 $ sbcbnRec mt nt
        sbcbnRec (BIT1 mt) (BIT0 nt) = doublebn =<< subbn mt nt
        sbcbnRec (BIT0 mt) (BIT1 nt) = doublebn =<< sbcbnRec mt nt
        sbcbnRec _ _ = fail "sbcbn"

topsplit :: MonadThrow m => HOLTerm -> m (Int, HOLTerm)
topsplit n@ZERO = return (0, n)
topsplit (BIT1 n@ZERO) = return (1, n)
topsplit (BIT0 (BIT1 n@ZERO)) = return (2, n)
topsplit (BIT1 (BIT1 n@ZERO)) = return (3, n)
topsplit (BIT0 (BIT0 (BIT1 n@ZERO))) = return (4, n)
topsplit (BIT1 (BIT0 (BIT1 n@ZERO))) = return (5, n)
topsplit (BIT0 (BIT1 (BIT1 n@ZERO))) = return (6, n)
topsplit (BIT1 (BIT1 (BIT1 n@ZERO))) = return (7, n)
topsplit (BIT0 (BIT0 (BIT0 (BIT0 n)))) = return (0, n)
topsplit (BIT1 (BIT0 (BIT0 (BIT0 n)))) = return (1, n)
topsplit (BIT0 (BIT1 (BIT0 (BIT0 n)))) = return (2, n)
topsplit (BIT1 (BIT1 (BIT0 (BIT0 n)))) = return (3, n)
topsplit (BIT0 (BIT0 (BIT1 (BIT0 n)))) = return (4, n)
topsplit (BIT1 (BIT0 (BIT1 (BIT0 n)))) = return (5, n)
topsplit (BIT0 (BIT1 (BIT1 (BIT0 n)))) = return (6, n)
topsplit (BIT1 (BIT1 (BIT1 (BIT0 n)))) = return (7, n)
topsplit (BIT0 (BIT0 (BIT0 (BIT1 n)))) = return (8, n)
topsplit (BIT1 (BIT0 (BIT0 (BIT1 n)))) = return (9, n)
topsplit (BIT0 (BIT1 (BIT0 (BIT1 n)))) = return (10, n)
topsplit (BIT1 (BIT1 (BIT0 (BIT1 n)))) = return (11, n)
topsplit (BIT0 (BIT0 (BIT1 (BIT1 n)))) = return (12, n)
topsplit (BIT1 (BIT0 (BIT1 (BIT1 n)))) = return (13, n)
topsplit (BIT0 (BIT1 (BIT1 (BIT1 n)))) = return (14, n)
topsplit (BIT1 (BIT1 (BIT1 (BIT1 n)))) = return (15, n)
topsplit _ = fail' "topsplit"
