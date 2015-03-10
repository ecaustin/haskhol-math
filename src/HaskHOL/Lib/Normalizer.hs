{-# LANGUAGE PatternSynonyms, ScopedTypeVariables #-}
{-|
  Module:    HaskHOL.Lib.Normalizer
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Normalizer
    ( convSEMIRING_NORMALIZERS
    , convNUM_NORMALIZE
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF
import HaskHOL.Lib.CalcNum

import Data.Vector (fromList, (!))

semiring_pth :: WFCtxt thry => HOL cls thry HOLThm
semiring_pth = cacheProof "semiring_pth" ctxtWF .
    prove [str| (!x:A y z. add x (add y z) = add (add x y) z) /\
                (!x y. add x y = add y x) /\
                (!x. add r0 x = x) /\
                (!x y z. mul x (mul y z) = mul (mul x y) z) /\
                (!x y. mul x y = mul y x) /\
                (!x. mul r1 x = x) /\
                (!x. mul r0 x = r0) /\
                (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
                (!x. pwr x 0 = r1) /\
                (!x n. pwr x (SUC n) = mul x (pwr x n))
                ==> (mul r1 x = x) /\
                    (add (mul a m) (mul b m) = mul (add a b) m) /\
                    (add (mul a m) m = mul (add a r1) m) /\
                    (add m (mul a m) = mul (add a r1) m) /\
                    (add m m = mul (add r1 r1) m) /\
                    (mul r0 m = r0) /\
                    (add r0 a = a) /\
                    (add a r0 = a) /\
                    (mul a b = mul b a) /\
                    (mul (add a b) c = add (mul a c) (mul b c)) /\
                    (mul r0 a = r0) /\
                    (mul a r0 = r0) /\
                    (mul r1 a = a) /\
                    (mul a r1 = a) /\
                    (mul (mul lx ly) (mul rx ry) = 
                     mul (mul lx rx) (mul ly ry)) /\
                    (mul (mul lx ly) (mul rx ry) = 
                     mul lx (mul ly (mul rx ry))) /\
                    (mul (mul lx ly) (mul rx ry) = 
                     mul rx (mul (mul lx ly) ry)) /\
                    (mul (mul lx ly) rx = mul (mul lx rx) ly) /\
                    (mul (mul lx ly) rx = mul lx (mul ly rx)) /\
                    (mul lx rx = mul rx lx) /\
                    (mul lx (mul rx ry) = mul (mul lx rx) ry) /\
                    (mul lx (mul rx ry) = mul rx (mul lx ry)) /\
                    (add (add a b) (add c d) = add (add a c) (add b d)) /\
                    (add (add a b) c = add a (add b c)) /\
                    (add a (add c d) = add c (add a d)) /\
                    (add (add a b) c = add (add a c) b) /\
                    (add a c = add c a) /\
                    (add a (add c d) = add (add a c) d) /\
                    (mul (pwr x p) (pwr x q) = pwr x (p + q)) /\
                    (mul x (pwr x q) = pwr x (SUC q)) /\
                    (mul (pwr x q) x = pwr x (SUC q)) /\
                    (mul x x = pwr x 2) /\
                    (pwr (mul x y) q = mul (pwr x q) (pwr y q)) /\
                    (pwr (pwr x p) q = pwr x (p * q)) /\
                    (pwr x 0 = r1) /\
                    (pwr x 1 = x) /\
                    (mul x (add y z) = add (mul x y) (mul x z)) /\
                    (pwr x (SUC q) = mul x (pwr x q)) |] $
      tacSTRIP `_THEN`
      _SUBGOAL_THEN [str| (!m:A n. add m n = add n m) /\
                          (!m n p. add (add m n) p = add m (add n p)) /\
                          (!m n p. add m (add n p) = add n (add m p)) /\
                          (!x. add x r0 = x) /\
                          (!m n. mul m n = mul n m) /\
                          (!m n p. mul (mul m n) p = mul m (mul n p)) /\
                          (!m n p. mul m (mul n p) = mul n (mul m p)) /\
                          (!m n p. mul (add m n) p = add (mul m p) (mul n p)) /\
                          (!x. mul x r1 = x) /\
                          (!x. mul x r0 = r0) |]
      tacMP `_THENL`
      [ tacASM_MESON_NIL
      , _MAP_EVERY (\ t -> _UNDISCH_THEN t (const _ALL))
        [ "!x:A y z. add x (add y z) = add (add x y) z"
        , "!x:A y. add x y :A = add y x"
        , "!x:A y z. mul x (mul y z) = mul (mul x y) z"
        , "!x:A y. mul x y :A = mul y x"
        ] `_THEN`
        tacSTRIP
      ] `_THEN`
      tacASM_REWRITE [ runConv convNUM =<< toHTm "2"
                     , runConv convNUM =<< toHTm "1" ] `_THEN`
      _SUBGOAL_THEN "!m n:num x:A. pwr x (m + n) :A = mul (pwr x m) (pwr x n)"
      tacASSUME `_THENL`
      [ tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]
      , _ALL
      ] `_THEN`
      _SUBGOAL_THEN "!x:A y:A n:num. pwr (mul x y) n = mul (pwr x n) (pwr y n)"
      tacASSUME `_THENL`
      [ tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE_NIL
      , _ALL
      ] `_THEN`
      _SUBGOAL_THEN "!x:A m:num n. pwr (pwr x m) n = pwr x (m * n)"
      (\ th -> tacASM_MESON [th]) `_THEN`
      tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [thmMULT_CLAUSES]

convSEMIRING_NORMALIZERS :: forall cls thry. WFCtxt thry
                         => HOLThm -> HOLThm 
                         -> ( HOLTerm -> Bool, Conversion cls thry
                            , Conversion cls thry, Conversion cls thry )
                         -> (HOLTerm -> HOLTerm -> Bool) -> 
                          HOL cls thry
                            ( Conversion cls thry, Conversion cls thry
                            , Conversion cls thry, Conversion cls thry
                            , Conversion cls thry, Conversion cls thry )
convSEMIRING_NORMALIZERS sth rth ( isSemiringConstant, convSEMIRING_ADD
                                 , convSEMIRING_MUL, convSEMIRING_POW ) 
                         variableOrder =
 do thms <- ruleCONJUNCTS =<< ruleMATCH_MP semiring_pth sth
    tmP <- serve tmP'
    tmQ <- serve tmQ'
    tmOnen <- serve tmOnen'
    tmZeron <- serve tmZeron' 
    tmTrue <- serve tmTrue'
    let pthms = fromList thms
        tmAdd = fromJust $ rator =<< rator =<< lHand (concl $ pthms ! 6)
        tmMul = fromJust $ rator =<< rator =<< lHand (concl $ pthms ! 12)
        tmPow = fromJust $ rator =<< rator =<< rand (concl $ pthms ! 31)
        tmZero = fromJust $ rand (concl $ pthms ! 5)
        tmOne = fromJust $ rand =<< lHand (concl $ pthms ! 13)
        ty = typeOf . fromJust . rand . concl $ pthms ! 0
        tmA = mkVar "a" ty
        tmB = mkVar "b" ty
        tmC = mkVar "c" ty
        tmD = mkVar "d" ty
        tmLX = mkVar "lx" ty
        tmLY = mkVar "ly" ty
        tmM = mkVar "m" ty
        tmRX = mkVar "rx" ty
        tmRY = mkVar "ry" ty
        tmX = mkVar "x" ty
        tmY = mkVar "y" ty
        tmZ = mkVar "z" ty
        destAdd = destBinop tmAdd
        destMul = destBinop tmMul
        destPow tm =
            do (l, r) <- destBinop tmPow tm
               if isNumeral r 
                  then Just (l, r)
                  else Nothing
        isAdd = isBinop tmAdd
        isMul = isBinop tmMul
    (nthm1, nthm2, tmSub, tmNeg, destSub) <-
          if concl rth == tmTrue 
          then return (rth, rth, tmTrue, tmTrue, \ t -> Just (t, t))
          else do nthm1 <- ruleSPEC tmX =<< ruleCONJUNCT1 rth
                  nthm2 <- ruleSPECL [tmX, tmY] =<< ruleCONJUNCT2 rth
                  let tmSub = fromJust $ rator =<< rator =<< lHand (concl nthm2)
                      tmNeg = fromJust $ rator =<< lHand (concl nthm1)
                      destSub = destBinop tmSub
                  return (nthm1, nthm2, tmSub, tmNeg, destSub)
--
    let convPOWVAR_MUL :: Conversion cls thry
        convPOWVAR_MUL = Conv $ \ tm ->
          let (l, r) = fromJust $ destMul tm in
            if isSemiringConstant l && isSemiringConstant r
            then runConv convSEMIRING_MUL tm
            else do { (lx, ln) <- liftO $ destPow l
                    ; do { (_, rn) <- liftO $ destPow r
                         ; th1 <- liftO . primINST [ (tmX, lx), (tmP, ln)
                                                   , (tmQ, rn) ] $ pthms ! 28
                         ; (tm1, tm2) <- liftO $ destComb =<< 
                                                   rand (concl th1)
                         ; th2 <- runConv convNUM_ADD tm2
                         ; liftO $ primTRANS th1 =<< ruleAP_TERM tm1 th2
                         } <|>
                      do { th1 <- liftO . primINST [ (tmX, lx)
                                                   , (tmQ, ln) ] $ pthms ! 30
                         ; (tm1, tm2) <- liftO $ destComb =<< 
                                                   rand (concl th1)
                         ; th2 <- runConv convNUM_SUC tm2
                         ; liftO $ primTRANS th1 =<< ruleAP_TERM tm1 th2
                         }
                    } <|>
                 do { (rx, rn) <- liftO $ destPow r
                    ; th1 <- liftO . primINST [(tmX, rx), (tmQ, rn)] $ pthms ! 29
                    ; (tm1, tm2) <- liftO $ destComb =<< rand (concl th1)
                    ; th2 <- runConv convNUM_SUC tm2
                    ; liftO $ primTRANS th1 =<< ruleAP_TERM tm1 th2
                    } <|> (liftO . primINST [(tmX, l)] $ pthms ! 31)
--
    let ruleMONOMIAL_DEONE :: HOLThm -> Maybe HOLThm
        ruleMONOMIAL_DEONE th =
            (do (l, r) <- destMul =<< rand (concl th)
                if l == tmOne
                   then hush $ primTRANS th #<< primINST [(tmX, r)] 
                                                  (pthms ! 0)
                   else return th)
            <|> return th
--
    let ruleMONOMIAL_POW :: HOLTerm -> HOLTerm -> HOLTerm 
                         -> HOL cls thry HOLThm
        ruleMONOMIAL_POW tm bod ntm
            | not (isComb bod) = return $! primREFL tm
            | isSemiringConstant bod = runConv convSEMIRING_POW tm
            | otherwise =
              let (lop, r) = fromJust $ destComb bod in
                if not (isComb lop) then return $! primREFL tm
                else let (op, l) = fromJust $ destComb lop in
                       if op == tmPow && isNumeral r
                       then let th1 = fromJust . primINST 
                                      [(tmX, l), (tmP, r), (tmQ, ntm)] $ pthms ! 33
                                (l', r') = fromJust $ destComb =<< 
                                                        rand (concl th1) in
                              do th2 <- runConv convNUM_MULT r'
                                 liftO $ primTRANS th1 =<< ruleAP_TERM l' th2
                       else if op == tmMul
                            then let th1 = fromJust . primINST
                                             [ (tmX, l), (tmY, r)
                                             , (tmQ, ntm) ] $ pthms ! 32
                                     (xy, z) = fromJust $ destComb =<<
                                                            rand (concl th1)
                                     (x, y) = fromJust $ destComb xy in
                                   do thl <- ruleMONOMIAL_POW y l ntm
                                      thr <- ruleMONOMIAL_POW z r ntm
                                      let thl' = fromRight $ ruleAP_TERM x thl
                                      liftO $ primTRANS th1 =<< 
                                                primMK_COMB thl' thr
                            else return $! primREFL tm
--
        convMONOMIAL_POW :: Conversion cls thry
        convMONOMIAL_POW = Conv $ \ tm ->
            let (lop, r) = fromJust $ destComb tm
                (op, l) = fromJust $ destComb lop in
              if op /= tmPow || not (isNumeral r)
              then fail "convMONOMIAL_POW"
              else if r == tmZeron then liftO . primINST [(tmX, l)] $ pthms ! 34
              else if r == tmOnen then liftO . primINST [(tmX, l)] $ pthms ! 35
              else do th <- ruleMONOMIAL_POW tm l r
                      liftO $ ruleMONOMIAL_DEONE th
--
    let powvar :: HOLTerm -> Maybe HOLTerm
        powvar tm
            | isSemiringConstant tm = Just tmOne
            | otherwise = 
                (do (lop, r) <- destComb tm
                    (op, l) <- destComb lop
                    if op == tmPow && isNumeral r
                       then Just l
                       else Nothing)
                <|> Just tm
--
        vorder :: HOLTerm -> HOLTerm -> Ordering
        vorder x y
            | x == y = EQ
            | x == tmOne = LT
            | y == tmOne = GT
            | variableOrder x y = LT
            | otherwise = GT
--
        ruleMONOMIAL_MUL :: HOLTerm -> HOLTerm -> HOLTerm 
                         -> HOL cls thry HOLThm
        ruleMONOMIAL_MUL tm l r =
          do { (lx, ly) <- liftO $ destMul l
             ; vl <- liftO $ powvar lx
             ; do { (rx, ry) <- liftO $ destMul r
                  ; vr <- liftO $ powvar rx
                  ; let ord = vorder vl vr
                  ; if ord == EQ
                    then do th1 <- liftO . primINST [ (tmLX, lx), (tmLY, ly)
                                                    , (tmRX, rx), (tmRY, ry) 
                                                    ] $ pthms ! 14
                            (tm1, tm2) <- liftO $ destComb =<<
                                                    rand (concl th1)
                            (tm3, tm4) <- liftO $ destComb tm1
                            th1_5 <- runConv convPOWVAR_MUL tm4
                            th2 <- liftO $ liftM1 ruleAP_THM 
                                             (ruleAP_TERM tm3 th1_5) tm2
                            th3 <- liftO $ primTRANS th1 th2
                            (tm5, tm6) <- liftO $ destComb =<<
                                                    rand (concl th3)
                            (tm7, tm8) <- liftO $ destComb tm6
                            tm7' <- liftO $ rand tm7
                            th4 <- ruleMONOMIAL_MUL tm6 tm7' tm8
                            liftO $ primTRANS th3 =<< ruleAP_TERM tm5 th4
                    else let th0 = (!) pthms $ if ord == LT then 15 
                                                else 16 in
                           do th1 <- liftO $ primINST 
                                               [ (tmLX, lx), (tmLY, ly)
                                               , (tmRX, rx), (tmRY, ry) ] th0
                              (tm1, tm2) <- liftO $ destComb =<< 
                                                      rand (concl th1)
                              (tm3, tm4) <- liftO $ destComb tm2
                              tm3' <- liftO $ rand tm3
                              th2 <- ruleMONOMIAL_MUL tm2 tm3' tm4
                              liftO $ primTRANS th1 =<< ruleAP_TERM tm1 th2
                  } <|>
               do { vr <- liftO $ powvar r
                  ; let ord = vorder vl vr
                  ; if ord == EQ
                    then do th1 <- liftO . primINST [ (tmLX, lx), (tmLY, ly)
                                                    , (tmRX, r) ] $ pthms ! 17
                            (tm1, tm2) <- liftO $ destComb =<< 
                                                    rand (concl th1)
                            (tm3, tm4) <- liftO $ destComb tm1
                            th1_5 <-  runConv convPOWVAR_MUL tm4
                            th2 <- liftO $ liftM1 ruleAP_THM 
                                             (ruleAP_TERM tm3 th1_5) tm2
                            liftO $ primTRANS th1 th2
                    else if ord == LT
                         then do th1 <- liftO . primINST 
                                                  [ (tmLX, lx), (tmLY, ly)
                                                  , (tmRX, r) ] $ pthms ! 18
                                 (tm1, tm2) <- liftO $ destComb =<< 
                                                         rand (concl th1)
                                 (tm3, tm4) <- liftO $ destComb tm2
                                 tm3' <- liftO $ rand tm3
                                 th2 <- ruleMONOMIAL_MUL tm2 tm3' tm4
                                 liftO $ primTRANS th1 =<< 
                                           ruleAP_TERM tm1 th2
                         else liftO . primINST [(tmLX, l), (tmRX, r)] $ 
                                        pthms ! 19
                  }
             } <|>
          do { vl <- liftO $ powvar l
             ; do { (rx, ry) <- liftO $ destMul r
                  ; vr <- liftO $ powvar rx
                  ; let ord = vorder vl vr
                  ; if ord == EQ
                    then do th1 <- liftO . primINST [ (tmLX, l), (tmRX, rx)
                                                    , (tmRY, ry) ] $ 
                                             pthms ! 20
                            (tm1, tm2) <- liftO $ destComb =<<
                                                    rand (concl th1)
                            (tm3, tm4) <- liftO $ destComb tm1
                            th2 <- runConv convPOWVAR_MUL tm4
                            liftO $ primTRANS th1 =<< liftM1 ruleAP_THM 
                                      (ruleAP_TERM tm3 th2) tm2
                    else if ord == GT
                         then do th1 <- liftO . primINST 
                                                  [ (tmLX, l), (tmRX, rx)
                                                  , (tmRY, ry) ] $ pthms ! 21
                                 (tm1, tm2) <- liftO $ destComb =<<
                                                         rand (concl th1)
                                 (tm3, tm4) <- liftO $ destComb tm2
                                 tm3' <- liftO $ rand tm3
                                 th2 <- ruleMONOMIAL_MUL tm2 tm3' tm4
                                 liftO $ primTRANS th1 =<< 
                                           ruleAP_TERM tm1 th2
                         else return $! primREFL tm
                  } <|>
               let vr = fromJust $ powvar r
                   ord = vorder vl vr in
                 if ord == EQ
                 then runConv convPOWVAR_MUL tm
                 else if ord == GT
                      then liftO . primINST [(tmLX, l), (tmRX, r)] $ pthms ! 19
                      else return $! primREFL tm
             }        
--
        convMONOMIAL_MUL :: Conversion cls thry
        convMONOMIAL_MUL = Conv $ \ tm ->
          let (l, r) = fromJust $ destMul tm in
            do th <- ruleMONOMIAL_MUL tm l r
               liftO $ ruleMONOMIAL_DEONE th
-- 
    let convPOLYNOMIAL_MONOMIAL_MUL :: Conversion cls thry
        convPOLYNOMIAL_MONOMIAL_MUL = Conv $ \ tm ->
          let (l, r) = fromJust $ destMul tm in
            (do (y, z) <- liftO $ destAdd r
                th1 <- liftO . primINST [(tmX, l), (tmY, y), (tmZ, z)] $ 
                                 pthms ! 36
                (tm1, tm2) <- liftO $ destComb =<< rand (concl th1)
                (tm3, tm4) <- liftO $ destComb tm1
                thl <- runConv convMONOMIAL_MUL tm4
                thr <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm2
                th2 <- liftO $ liftM1 primMK_COMB (ruleAP_TERM tm3 thl) thr
                liftO $ primTRANS th1 th2)
            <|> runConv convMONOMIAL_MUL tm
--
    let convMONOMIAL_ADD :: Conversion cls thry
        convMONOMIAL_ADD = Conv $ \ tm ->
          let (l, r) = fromJust $ destAdd tm in
            if isSemiringConstant l && isSemiringConstant r
            then runConv convSEMIRING_ADD tm
            else let th1 = fromJust $
                       let ll' = lHand l
                           lr' = lHand r in
                         if isMul l && 
                            (liftM isSemiringConstant ll' == Just True)
                         then if isMul r && 
                                 (liftM isSemiringConstant lr' == Just True)
                              then do rr <- rand r
                                      ll <- ll'
                                      lr <- lr'
                                      primINST [ (tmA, ll), (tmB, lr)
                                               , (tmM, rr) ] $ pthms ! 1
                              else do ll <- ll'
                                      primINST [(tmA, ll),(tmM, r)] $ 
                                        pthms ! 2
                         else if isMul r && 
                                 (liftM isSemiringConstant lr' == Just True)
                              then do lr <- lr'
                                      primINST [(tmA, lr), (tmM, l)] $ 
                                        pthms ! 3
                              else primINST [(tmM, r)] $ pthms ! 4
                     (tm1, tm2) = fromJust $ destComb =<< rand (concl th1)
                     (tm3, tm4) = fromJust $ destComb tm1 in
                   do th1_5 <- runConv convSEMIRING_ADD tm4
                      let th2 = fromRight $ ruleAP_TERM tm3 th1_5
                          th3 = fromRight $ primTRANS th1 =<<
                                              ruleAP_THM th2 tm2
                          tm5 = fromJust . rand $ concl th3
                      if lHand tm5 == Just tmZero
                         then let tm5' = fromJust $ rand tm5 in
                                liftO $ primTRANS th3 #<< 
                                          primINST [(tmM, tm5')] (pthms ! 5)
                         else liftO $ ruleMONOMIAL_DEONE th3
--
    let powervars :: HOLTerm -> [HOLTerm]
        powervars tm =
            let ptms = stripList destMul tm in
              if isSemiringConstant $ head ptms
              then tail ptms
              else ptms

        destVarpow :: HOLTerm -> Maybe (HOLTerm, Integer)
        destVarpow tm =
            (do (x, n) <- destPow tm
                n' <- destNumeral n
                return (x, n'))
            <|> return (tm, if isSemiringConstant tm then 0 else 1)

        morder :: HOLTerm -> HOLTerm -> Ordering
        morder tm1 tm2 =
            let vdegs1 = fromJust . mapM destVarpow $ powervars tm1
                vdegs2 = fromJust . mapM destVarpow $ powervars tm2
                deg1 = foldr ((+) . snd) 0 vdegs1
                deg2 = foldr ((+) . snd) 0 vdegs2 in
              if deg1 < deg2 then LT
              else if deg1 > deg2 then GT
                   else lexorder vdegs1 vdegs2
          where lexorder :: [(HOLTerm, Integer)] -> [(HOLTerm, Integer)] 
                         -> Ordering
                lexorder [] [] = EQ
                lexorder _ [] = LT
                lexorder [] _ = GT
                lexorder ((x1, n1):vs1) ((x2, n2):vs2)
                    | variableOrder x1 x2 = GT
                    | variableOrder x2 x1 = LT
                    | n1 < n2 = LT
                    | n2 < n1 = GT
                    | otherwise = lexorder vs1 vs2
--
    let ruleDEZERO :: HOLThm -> Either String HOLThm
        ruleDEZERO th =
            do tm <- note "" . rand $ concl th
               if not (isAdd tm)
                  then return th
                  else do (lop, r) <- note "" $ destComb tm
                          l <- note "" $ rand lop
                          if l == tmZero
                             then primTRANS th #<< primINST [(tmA, r)] (pthms ! 6)
                             else if r == tmZero
                                  then primTRANS th #<< 
                                         primINST [(tmA, l)] (pthms ! 7)
                                  else return th

        convPOLYNOMIAL_ADD :: Conversion cls thry
        convPOLYNOMIAL_ADD = Conv $ \ tm ->
          let (l, r) = fromJust $ destAdd tm in
            if l == tmZero then liftO . primINST [(tmA, r)] $ pthms ! 6
            else if r == tmZero then liftO . primINST [(tmA, l)] $ pthms ! 7
            else if isAdd l
                 then let (a, b) = fromJust $ destAdd l in
                        if isAdd r
                        then let (c, d) = fromJust $ destAdd r
                                 ord = morder a c in
                               if ord == EQ
                               then let th1 = fromJust . primINST 
                                                [ (tmA, a), (tmB, b), (tmC, c)
                                                , (tmD, d) ] $ pthms ! 22
                                        (tm1, tm2) = fromJust $ destComb =<<
                                                       rand (concl th1)
                                        (tm3, tm4) = fromJust $ destComb tm1 in
                                      do th1_5 <- runConv convMONOMIAL_ADD tm4  
                                         let th2 = fromRight $ 
                                                     ruleAP_TERM tm3 th1_5
                                         th3 <- runConv convPOLYNOMIAL_ADD tm2 
                                         liftO $ ruleDEZERO =<< 
                                                 primTRANS th1 =<<
                                                 primMK_COMB th2 th3
                               else let th1 = fromJust $ 
                                              if ord == GT 
                                              then primINST [ (tmA, a), (tmB, b)
                                                            , (tmC, r) ] $ pthms ! 23
                                              else primINST [ (tmA, l), (tmC, c)
                                                            , (tmD, d) ] $ pthms ! 24
                                        (tm1, tm2) = fromJust $ destComb =<<
                                                       rand (concl th1) in
                                      do th2 <- runConv convPOLYNOMIAL_ADD tm2
                                         liftO $ ruleDEZERO =<<
                                                 primTRANS th1 =<<
                                                 ruleAP_TERM tm1 th2
                        else let ord = morder a r in
                               if ord == EQ
                               then let th1 = fromJust $ primINST [(tmA, a), (tmB, b), (tmC, r)] (pthms ! 25)
                                        (tm1, tm2) = fromJust $ destComb =<< rand (concl th1)
                                        (tm3, tm4) = fromJust $ destComb tm1 in
                                      do thl <- runConv convMONOMIAL_ADD tm4
                                         let th2 = fromRight $ liftM1 ruleAP_THM (ruleAP_TERM tm3 thl) tm2
                                         liftO $ ruleDEZERO =<< primTRANS th1 th2
                               else if ord == GT
                                    then let th1 = fromJust $ primINST [(tmA, a), (tmB, b), (tmC, r)] (pthms ! 23)
                                             (tm1, tm2) = fromJust $ destComb =<< rand (concl th1) in
                                           do th <- runConv convPOLYNOMIAL_ADD tm2
                                              liftO $ ruleDEZERO =<< primTRANS th1 =<< ruleAP_TERM tm1 th
                                    else liftO $ ruleDEZERO #<< 
                                           primINST [(tmA, l), (tmC, r)] (pthms ! 26)
                else if isAdd r
                     then let (c, d) = fromJust $ destAdd r
                              ord = morder l c in
                            if ord == EQ
                            then let th1 = fromJust . primINST 
                                                         [ (tmA, l), (tmC, c)
                                                         , (tmD, d) ] $ pthms ! 27
                                     (tm1, tm2) = fromJust $ destComb =<< 
                                                               rand (concl th1)
                                     (tm3, tm4) = fromJust $ destComb tm1 in
                                   do th1_5 <- runConv convMONOMIAL_ADD tm4
                                      let th2 = fromRight $ liftM1 ruleAP_THM
                                                  (ruleAP_TERM tm3 th1_5) tm2
                                      liftO $ ruleDEZERO =<< primTRANS th1 th2
                            else if ord == GT
                                 then return $! primREFL tm
                                 else let th1 = fromJust . primINST 
                                                  [ (tmA, l), (tmC, c)
                                                  , (tmD, d) ] $ pthms ! 24
                                          (tm1, tm2) = fromJust $ destComb =<< 
                                                         rand (concl th1) in
                                        do th2 <- runConv convPOLYNOMIAL_ADD tm2
                                           liftO $ ruleDEZERO =<< primTRANS th1 =<<
                                                     ruleAP_TERM tm1 th2
                     else let ord = morder l r in
                            if ord == EQ
                            then runConv convMONOMIAL_ADD tm
                            else if ord == GT 
                                 then liftO . ruleDEZERO $ primREFL tm
                                 else liftO $ ruleDEZERO #<< 
                                        primINST [(tmA, l), (tmC, r)] (pthms ! 26)
--                    
    let rulePMUL :: HOLTerm -> HOL cls thry HOLThm
        rulePMUL tm =
          let (l, r) = fromJust $ destMul tm in
            if not (isAdd l) then runConv convPOLYNOMIAL_MONOMIAL_MUL tm
            else if not (isAdd r)
                 then let th1 = fromJust . 
                                  primINST [(tmA, l), (tmB, r)] $ pthms ! 8 in
                        do th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL #<<
                                    rand (concl th1)
                           liftO $ primTRANS th1 th2
                 else let (a, b) = fromJust $ destAdd l
                          th1 = fromJust . 
                                  primINST [(tmA, a), (tmB, b), (tmC, r)] $ pthms ! 109
                          (tm1, tm2) = fromJust $ destComb =<< rand (concl th1)
                          (tm3, tm4) = fromJust $ destComb tm1 in
                        do th1_5 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm4
                           let th2 = fromRight $ ruleAP_TERM tm3 th1_5
                           th2_5 <- rulePMUL tm2
                           let th3 = fromRight $ primTRANS th1 =<< 
                                                   primMK_COMB th2 th2_5
                           th4 <- runConv convPOLYNOMIAL_ADD #<< 
                                    rand (concl th3)
                           liftO $ primTRANS th3 th4

        convPOLYNOMIAL_MUL :: Conversion cls thry
        convPOLYNOMIAL_MUL = Conv $ \ tm ->
            let (l, r) = fromJust $ destMul tm in
              if l == tmZero 
              then liftO . primINST [(tmA, r)] $ pthms ! 10
              else if r == tmZero 
                   then liftO . primINST [(tmA, l)] $ pthms ! 11
              else if l == tmOne 
                   then liftO . primINST [(tmA, r)] $ pthms ! 12
              else if r == tmOne 
                   then liftO . primINST [(tmA, l)] $ pthms ! 13
              else rulePMUL tm
--
    let rulePPOW :: HOLTerm -> HOL cls thry HOLThm
        rulePPOW tm =
            let (l, n) = fromJust $ destPow tm in
              if n == tmZeron then liftO $ primINST [(tmX, l)] $ pthms ! 34
              else if n == tmOnen then liftO $ 
                                         primINST [(tmX, l)] $ pthms ! 35
              else do th1 <- runConv convNUM n
                      let qtm' = fromJust $ rand =<< rand (concl th1)
                          th2 = fromJust . primINST 
                                  [(tmX, l), (tmQ, qtm')] $ pthms ! 37
                          (tm1, tm2) = fromJust $ destComb =<< 
                                                    rand (concl th2)
                      thr <- rulePPOW tm2
                      let th3 = fromRight $ primTRANS th2 =<< 
                                              ruleAP_TERM tm1 thr
                          tm' = fromJust $ rator tm
                          th4 = fromRight $ 
                                  liftM1 primTRANS (ruleAP_TERM tm' th1) th3
                      th5 <- runConv convPOLYNOMIAL_MUL #<< rand (concl th4)
                      liftO $ primTRANS th4 th5

        convPOLYNOMIAL_POW :: Conversion cls thry
        convPOLYNOMIAL_POW = Conv $ \ tm ->
            if isAdd (fromJust $ lHand tm)
            then rulePPOW tm
            else runConv convMONOMIAL_POW tm
--         
    let convPOLYNOMIAL_NEG :: Conversion cls thry
        convPOLYNOMIAL_NEG = Conv $ \ tm ->
            let (l, r) = fromJust $ destComb tm in
              if l /= tmNeg then fail "convPOLYNOMIAL_NEG"
              else let th1 = fromJust $ primINST [(tmX, r)] nthm1 in
                     do th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL #<<
                                 rand (concl th1)
                        liftO $ primTRANS th1 th2
--
    let convPOLYNOMIAL_SUB :: Conversion cls thry
        convPOLYNOMIAL_SUB = Conv $ \ tm ->
            let (l, r) = fromJust $ destSub tm
                th1 = fromJust $ primINST [(tmX, l), (tmY, r)] nthm2
                (tm1, tm2) = fromJust $ destComb =<< rand (concl th1) in
              do thr1 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm2
                 let th2 = fromRight $ ruleAP_TERM tm1 thr1
                 thr2 <- runConv convPOLYNOMIAL_ADD #<< rand (concl th2)
                 liftO $ primTRANS th1 =<< primTRANS th2 thr2
--
    let convPOLYNOMIAL :: Conversion cls thry
        convPOLYNOMIAL = Conv $ \ tm ->
          if not (isComb tm) || isSemiringConstant tm
          then return $! primREFL tm
          else let (lop, r) = fromJust $ destComb tm in 
                 if lop == tmNeg
                 then do th0_5 <- runConv convPOLYNOMIAL r
                         let th1 = fromRight $ ruleAP_TERM lop th0_5
                         th2 <- runConv convPOLYNOMIAL_NEG #<< rand (concl th1)
                         liftO $ primTRANS th1 th2
                 else if not (isComb lop)
                      then return $! primREFL tm
                      else let (op, l) = fromJust $ destComb lop in
                             if op == tmPow && isNumeral r
                             then do th0_5 <- runConv convPOLYNOMIAL l
                                     let th1 = fromRight $ liftM1
                                             ruleAP_THM (ruleAP_TERM op th0_5) r
                                     th2 <- runConv convPOLYNOMIAL_POW #<< 
                                              rand (concl th1)
                                     liftO $ primTRANS th1 th2
                             else if op == tmAdd || op == tmMul || op == tmSub
                                  then do thl <- runConv convPOLYNOMIAL l
                                          thr <- runConv convPOLYNOMIAL r
                                          let th1 = fromRight $ liftM1 
                                                primMK_COMB (ruleAP_TERM op thl) thr
                                              fn 
                                                | op == tmAdd =
                                                    convPOLYNOMIAL_ADD
                                                | op == tmMul =
                                                    convPOLYNOMIAL_MUL
                                                | otherwise = 
                                                    convPOLYNOMIAL_SUB
                                          th2 <- runConv fn #<< rand (concl th1)
                                          liftO $ primTRANS th1 th2
                                  else return $! primREFL tm
--
    return ( convPOLYNOMIAL_NEG, convPOLYNOMIAL_ADD, convPOLYNOMIAL_SUB
           , convPOLYNOMIAL_MUL, convPOLYNOMIAL_POW, convPOLYNOMIAL )

tmTrue', tmP', tmQ', tmZeron', tmOnen' :: WFCtxt thry => PTerm thry
tmTrue' = [wF| T |]
tmP' = [wF| p:num |]
tmQ' = [wF| q:num |]
tmZeron' = [wF| 0 |]
tmOnen' = [wF| 1 |]

convNUM_NORMALIZE_sth :: WFCtxt thry => HOL cls thry HOLThm
convNUM_NORMALIZE_sth = cacheProof "convNUM_NORMALIZE_sth" ctxtWF $
    prove [str| (!x y z. x + (y + z) = (x + y) + z) /\
                (!x y. x + y = y + x) /\
                (!x. 0 + x = x) /\
                (!x y z. x * (y * z) = (x * y) * z) /\
                (!x y. x * y = y * x) /\
                (!x. 1 * x = x) /\
                (!x. 0 * x = 0) /\
                (!x y z. x * (y + z) = x * y + x * z) /\
                (!x. x EXP 0 = 1) /\
                (!x n. x EXP (SUC n) = x * x EXP n) |] $
      tacREWRITE [ defEXP, thmMULT_CLAUSES, thmADD_CLAUSES
                 , thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmADD_AC, thmMULT_AC]

convNUM_NORMALIZE :: WFCtxt thry => Conversion cls thry
convNUM_NORMALIZE = Conv $ \ tm ->
    do sth <- convNUM_NORMALIZE_sth
       rth <- thmTRUTH
       (_, _, _, _, _, conv) <- convSEMIRING_NORMALIZERS sth rth
          (isNumeral, convNUM_ADD, convNUM_MULT, convNUM_EXP) (<)
       runConv conv tm
                       
