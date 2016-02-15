{-# LANGUAGE ScopedTypeVariables #-}
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
    prove [txt| (!x:A y z. add x (add y z) = add (add x y) z) /\
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
      _SUBGOAL_THEN [txt| (!m:A n. add m n = add n m) /\
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
        [ [txt| !x:A y z. add x (add y z) = add (add x y) z |]
        , [txt| !x:A y. add x y :A = add y x |]
        , [txt| !x:A y z. mul x (mul y z) = mul (mul x y) z |]
        , [txt| !x:A y. mul x y :A = mul y x |]
        ] `_THEN`
        tacSTRIP
      ] `_THEN`
      tacASM_REWRITE [ runConv convNUM [txt| 2 |]
                     , runConv convNUM [txt| 1 |] ] `_THEN`
      _SUBGOAL_THEN [txt| !m n:num x:A. pwr x (m + n) :A = 
                                        mul (pwr x m) (pwr x n) |]
      tacASSUME `_THENL`
      [ tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE [thmADD_CLAUSES]
      , _ALL
      ] `_THEN`
      _SUBGOAL_THEN [txt| !x:A y:A n:num. pwr (mul x y) n = 
                                          mul (pwr x n) (pwr y n) |]
      tacASSUME `_THENL`
      [ tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN` tacASM_REWRITE_NIL
      , _ALL
      ] `_THEN`
      _SUBGOAL_THEN [txt| !x:A m:num n. pwr (pwr x m) n = pwr x (m * n) |]
      (\ th -> tacASM_MESON [th]) `_THEN`
      tacGEN `_THEN` tacGEN `_THEN` tacINDUCT `_THEN` 
      tacASM_REWRITE [thmMULT_CLAUSES]


reverseInterface :: Text -> Text -> HOLType -> HOL cls thry Bool
reverseInterface op s ty =
    can (findM (\ (op', s', ty') ->
                    do cond' <- can (typeMatch ty') ty
                       return $! cond' && op == op' && s' == s)) `fmap`
      getInterface

-- Interface based destructors
-- Do we want to memoize these?  Should probably profile that.
destBinary :: Text -> HOLTerm -> HOL cls thry (HOLTerm, HOLTerm)
destBinary op tm@(Binary s l r) =
    do cond <- reverseInterface op s $ typeOf tm
       if cond
          then return (l, r)
          else fail "destBinary: not a defined overloading of multiplication."
destBinary _ = fail "destBinary: not a binary term."

destMul :: HOLTerm -> HOL cls thry (HOLTerm, HOLTerm)
destMul = destBinary "*"

destPow :: HOLTerm -> HOL cls thry (HOLTerm, HOLTerm)
destPow = destBinary "^"

data SemiRingContext = SemiRingContext
    { ty      :: !HOLType
    , mulName :: !Text
    , powName :: !Text
    , pthms   :: !(Vector HOLThm)
    }

convPOWVAR_MUL :: SemiRingContext -> Conversion cls thry
convPOWVAR_MUL ctxt = Conv $ \ tm ->
    case tm of
      (Binary' (mulName ctxt) l r)
          | isSemiringConstant l && isSemiringConstant r ->
              runConv convSEMIRING_MUL tm
          | otherwise ->
              case l of
                (Binary' (powName ctxt) lx ln) ->
                    case r of
                      (Binary' (powName ctxt) _ rn) ->
                          do tmX <- mkVar "x" (ty ctxt)
                             tmP <- mkVar "p" (ty ctxt)
                             tmQ <- mkVar "q" (ty ctxt)
                             th1 <- primINST [(tmX, lx), (tmP, ln), (tmQ, rn)] $
                                      (pthms ctxt) ! 28
                             (tm1, tm2) <- destComb =<< rand (concl th1)
                             th2 <- runConv convNUM_ADD tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                      _ ->
                          do tmX <- mkVar "x" (ty ctxt)
                             tmQ <- mkVar "q" (ty ctxt)
                             th1 <- primINST [(tmX, lx), (tmQ, ln)] $ 
                                      (pthms ctxt) ! 30
                             (tm1, tm2) <- destComb =<< rand (concl th1)
                             th2 <- runConv convNUM_SUC tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                _ ->
                    case r of
                      (Binary' (powName ctxt) rx rn) ->
                          do tmX <- mkVar "x" (ty ctxt)
                             tmQ <- mkVar "q" (ty ctxt)
                             th1 <- primINST [(tmX, rx), (tmQ, rn)] $ 
                                      (pthms ctxt) ! 29
                             (tm1, tm2) <- destComb =<< rand (concl th1)
                             th2 <- runConv convNUM_SUC tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                      _ -> do tmX <- mkVar "x" (ty ctxt)
                              primINST [(tmX, l)] $ (ctxt pthms) ! 31

ruleMONOMIAL_DEONE :: SemiringContext -> HOLThm -> Maybe HOLThm
ruleMONOMIAL_DEONE ctxt th@(HOLThm (Comb _ tm) =
    case tm of
      (Binary' (mulName ctxt) l r)
          | l == (tmOne ctxt) ->
              do tmX <- mkVar "x" (ty ctxt)
                 primTRANS th . primINST [(tmX, r)] $ (pthms ctxt) ! 0
          | otherwise -> return th
ruleMONOMIAL_DEONE _ th = return th

ruleMONOMIAL_POW :: SemiringContext -> HOLTerm -> HOLTerm -> HOLTerm 
                 -> HOL cls thry HOLThm
ruleMONOMIAL_POW ctxt tm bod ntm =
    case bod of
      (Comb lop r)
          | isSemiringConstant bod -> runConv convSEMIRING_POW tm
          | otherwise ->
              case lop of
                (Comb op l)
                    | op == tmPow && isNumeral r ->
                        do tmX <- mkVar "x" (ty ctxt)
                           tmP <- mkVar "p" (ty ctxt)
                           tmQ <- mkVar "q" (ty ctxt)
                           th1 <- primINST [(tmX, l), (tmP, r), (tmQ, ntm)] $
                                    (pthms ctxt) ! 33
                           (l', r') <- destComb $ rand (concl th1)
                           th2 <- runConv convNUM_MULT r'
                           primTRANS th1 $ ruleAP_TERM l' th2
                    | op == tmMul ->
                        do tmX <- mkVar "x" (ty ctxt)
                           tmY <- mkVar "y" (ty ctxt)
                           tmQ <- mkVar "q" (ty ctxt)
                           th1 <- primINST [(tmX, l), (tmY, r), (tmQ, ntm)] $ 
                                    (pthms ctxt) ! 32
                           (xy, z) <- destComb $ rand (concl th1)
                           (x, y) <- destComb xy
                           thl <- ruleMONOMIAL_POW y l ntm
                           thr <- ruleMONOMIAL_POW z r ntm
                           thl' <- ruleAP_TERM x thl
                           primTRANS th1 $ primMK_COMB thl' thr
                    | otherwise -> primREFL tm
                _ -> primREFL tm
      _ -> primREFL tm

convMONOMIAL_POW :: SemiRingContext -> Conversion cls thry
convMONOMIAL_POW ctxt = Conv $ \ tm ->
    do (lop, r) <- destComb tm
       (op, l) <- destComb lop
       tmX <- mkVar "x" (ty ctxt)
       if op /= tmPow || not (isNumeral r)
          then fail "convMONOMIAL_POW"
          else if r == tmZeron then primINST [(tmX, l)] $ (pthms ctxt) ! 34
          else if r == tmOnen then primINST [(tmX, l)] $ (pthms ctxt) ! 35
          else do th <- ruleMONOMIAL_POW tm l r
                  ruleMONOMIAL_DEONE th

ruleMONOMIAL_MUL :: SemiRingContext -> HOLTerm -> HOLTerm -> HOLTerm 
                 -> HOL cls thry HOLThm
ruleMONOMIAL_MUL ctxt tm l r =
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

  where powvar :: HOLTerm -> HOL cls thry HOLTerm
        powvar tm
            | isSemiringConstant tm = return tmOne
            | otherwise = 
                case tm of
                  (Comb lop r) ->
                      case lop of
                        (Comb op l)
                            | op == tmPow && isNumeral r -> return l
                            | otherwise -> fail "powvar"
                        _ -> return tm
                  _ -> return tm

        vorder :: HOLTerm -> HOLTerm -> Ordering
        vorder x y
            | x == y = EQ
            | x == tmOne = LT
            | y == tmOne = GT
            | variableOrder x y = LT
            | otherwise = GT

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
 do thms <- ruleCONJUNCTS $ ruleMATCH_MP semiring_pth sth
    let pthms = fromList thms
    tmAdd <- rator . rator . lHand . concl $ pthms ! 6
    tmMul <- rator . rator . lHand . concl $ pthms ! 12
    tmPow <- rator . rator . rand . concl $ pthms ! 31
    tmZero <- rand . concl $ pthms ! 5
    tmOne <- rand . lHand . concl $ pthms ! 13
    ty <- typeOf `fmap` (rand . concl $ pthms ! 0)
    tmA <-  mkVar "a" ty
    tmB <- mkVar "b" ty
    tmC <- mkVar "c" ty
    tmD <- mkVar "d" ty
    tmLX <- mkVar "lx" ty
    tmLY <- mkVar "ly" ty
    tmM <- mkVar "m" ty
    tmRX <- mkVar "rx" ty
    tmRY <- mkVar "ry" ty
    tmX <- mkVar "x" ty
    tmY <- mkVar "y" ty
    tmZ <- mkVar "z" ty
    let destAdd = destBinop tmAdd
        destMul = destBinop tmMul
        destPow tm =
            do (l, r) <- destBinop tmPow tm
               if isNumeral r 
                  then return (l, r)
                  else fail' "destPow"
        isAdd = isBinop tmAdd
        isMul = isBinop tmMul
    (nthm1, nthm2, tmSub, tmNeg, destSub) <-
          if concl rth == tmTrue 
          then return (rth, rth, tmTrue, tmTrue, \ t -> return (t, t))
          else do nthm1 <- ruleSPEC tmX $ ruleCONJUNCT1 rth
                  nthm2 <- ruleSPECL [tmX, tmY] $ ruleCONJUNCT2 rth
                  tmSub <- rator =<< rator =<< lHand (concl nthm2)
                  tmNeg <- rator =<< lHand (concl nthm1)
                  let destSub = destBinop tmSub
                  return (nthm1, nthm2, tmSub, tmNeg, destSub)     
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
          do (l, r) <- destAdd tm
             if l == tmZero then primINST [(tmA, r)] $ pthms ! 6
             else if r == tmZero then primINST [(tmA, l)] $ pthms ! 7
             else if isAdd l
                  then do (a, b) <- destAdd l
                          if isAdd r
                          then do (c, d) <- destAdd r
                                  let ord = morder a c
                                  if ord == EQ
                                     then do th1 <- primINST 
                                                      [ (tmA, a), (tmB, b)
                                                      , (tmC, c), (tmD, d) ] $ 
                                                      pthms ! 22
                                             (tm1, tm2) <- destComb =<<
                                                             rand (concl th1)
                                             (tm3, tm4) <- destComb tm1
                                             th1_5 <- runConv convMONOMIAL_ADD tm4  
                                             th2 <- ruleAP_TERM tm3 th1_5
                                             th3 <- runConv convPOLYNOMIAL_ADD tm2 
                                             ruleDEZERO =<< 
                                               primTRANS th1 =<<
                                               primMK_COMB th2 th3
                                     else do th1 <- if ord == GT 
                                                    then primINST [ (tmA, a), (tmB, b)
                                                                  , (tmC, r) ] $ pthms ! 23
                                                    else primINST [ (tmA, l), (tmC, c)
                                                                  , (tmD, d) ] $ pthms ! 24
                                                         (tm1, tm2) <- destComb =<< rand (concl th1)
                                             th2 <- runConv convPOLYNOMIAL_ADD tm2
                                             ruleDEZERO =<<
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
          do (l, r) <- destMul tm
             if not (isAdd l) then runConv convPOLYNOMIAL_MONOMIAL_MUL tm
             else if not (isAdd r)
                  then do th1 <- primINST [(tmA, l), (tmB, r)] $ pthms ! 8
                          th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL $
                                   rand (concl th1)
                          primTRANS th1 th2
                  else do (a, b) <- destAdd l
                          th1 <- primINST [(tmA, a), (tmB, b), (tmC, r)] $ 
                                   pthms ! 109
                          (tm1, tm2) <- destComb =<< rand (concl th1)
                          (tm3, tm4) <- destComb tm1
                          th1_5 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm4
                          th2 <- ruleAP_TERM tm3 th1_5
                          th2_5 <- rulePMUL tm2
                          th3 <- primTRANS th1 =<< primMK_COMB th2 th2_5
                          th4 <- runConv convPOLYNOMIAL_ADD $ rand (concl th3)
                          primTRANS th3 th4

        convPOLYNOMIAL_MUL :: Conversion cls thry
        convPOLYNOMIAL_MUL = Conv $ \ tm ->
            do (l, r) <- destMul tm
               if l == tmZero 
                  then primINST [(tmA, r)] $ pthms ! 10
                  else if r == tmZero then primINST [(tmA, l)] $ pthms ! 11
                  else if l == tmOne then primINST [(tmA, r)] $ pthms ! 12
                  else if r == tmOne then primINST [(tmA, l)] $ pthms ! 13
                  else rulePMUL tm
--
    let rulePPOW :: HOLTerm -> HOL cls thry HOLThm
        rulePPOW tm =
            do (l, n) <- destPow tm
               if n == tmZeron then primINST [(tmX, l)] $ pthms ! 34
               else if n == tmOnen then primINST [(tmX, l)] $ pthms ! 35
               else do th1 <- runConv convNUM n
                       qtm' <- rand =<< rand (concl th1)
                       th2 <- primINST [(tmX, l), (tmQ, qtm')] $ pthms ! 37
                       (tm1, tm2) <- destComb =<< rand (concl th2)
                       thr <- rulePPOW tm2
                       th3 <- primTRANS th2 =<< ruleAP_TERM tm1 thr
                       tm' <- rator tm
                       th4 <- primTRANS (ruleAP_TERM tm' th1) th3
                       th5 <- runConv convPOLYNOMIAL_MUL $ rand (concl th4)
                       primTRANS th4 th5

        convPOLYNOMIAL_POW :: Conversion cls thry
        convPOLYNOMIAL_POW = Conv $ \ tm ->
            do l <- lHand tm
               if isAdd l
                  then rulePPOW tm
                  else runConv convMONOMIAL_POW tm
--         
    let convPOLYNOMIAL_NEG :: Conversion cls thry
        convPOLYNOMIAL_NEG = Conv $ \ tm ->
            do (l, r) <- destComb tm
               if l /= tmNeg then fail "convPOLYNOMIAL_NEG"
               else do th1 <- primINST [(tmX, r)] nthm1
                       th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL $ 
                                rand (concl th1)
                       primTRANS th1 th2
--
    let convPOLYNOMIAL_SUB :: Conversion cls thry
        convPOLYNOMIAL_SUB = Conv $ \ tm ->
            do (l, r) <- destSub tm
               th1 <- primINST [(tmX, l), (tmY, r)] nthm2
               (tm1, tm2) <- destComb $ rand (concl th1)
               thr1 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm2
               th2 <- ruleAP_TERM tm1 thr1
               thr2 <- runConv convPOLYNOMIAL_ADD $ rand (concl th2)
               primTRANS th1 $ primTRANS th2 thr2
--
    let convPOLYNOMIAL :: Conversion cls thry
        convPOLYNOMIAL = Conv $ \ tm ->
          if isSemiringConstant tm then primREFL tm
          else case tm of
                 (Comb lop r)
                     | lop == tmNeg ->
                         do th0_5 <- runConv convPOLYNOMIAL r
                            th1 <- ruleAP_TERM lop th0_5
                            th2 <- runConv convPOLYNOMIAL_NEG $ rand (concl th1)
                            primTRANS th1 th2
                     | otherwise ->
                         case lop of
                           (Comb op l)
                               | op == tmPow && isNumeral r ->
                                   do th0_5 <- runConv convPOLYNOMIAL l
                                      th1 <- ruleAP_THM (ruleAP_TERM op th0_5) r
                                      th2 <- runConv convPOLYNOMIAL_POW $ 
                                               rand (concl th1)
                                      primTRANS th1 th2
                               | op == tmAdd || op == tmMul || op == tmSub ->
                                   do thl <- runConv convPOLYNOMIAL l
                                      thr <- runConv convPOLYNOMIAL r
                                      th1 <- primMK_COMB (ruleAP_TERM op thl) 
                                               thr
                                      let fn 
                                              | op == tmAdd = convPOLYNOMIAL_ADD
                                              | op == tmMul = convPOLYNOMIAL_MUL
                                              | otherwise = convPOLYNOMIAL_SUB
                                      th2 <- runConv fn $ rand (concl th1)
                                      primTRANS th1 th2
                               | otherwise -> primREFL tm
                           _ -> primREFL tm
                 _ -> primREFL tm
--
    return ( convPOLYNOMIAL_NEG, convPOLYNOMIAL_ADD, convPOLYNOMIAL_SUB
           , convPOLYNOMIAL_MUL, convPOLYNOMIAL_POW, convPOLYNOMIAL )

tmTrue', tmP', tmQ', tmZeron', tmOnen' :: WFCtxt thry => PTerm thry
tmTrue' = [wf| T |]
tmP' = [wf| p:num |]
tmQ' = [wf| q:num |]
tmZeron' = [wf| 0 |]
tmOnen' = [wf| 1 |]

convNUM_NORMALIZE_sth :: WFCtxt thry => HOL cls thry HOLThm
convNUM_NORMALIZE_sth = cacheProof "convNUM_NORMALIZE_sth" ctxtWF $
    prove [txt| (!x y z. x + (y + z) = (x + y) + z) /\
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
                       
