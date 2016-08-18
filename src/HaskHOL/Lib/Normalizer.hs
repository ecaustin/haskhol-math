{-# LANGUAGE ImplicitParams, ScopedTypeVariables #-}
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
import qualified HaskHOL.Core.Basics as B (destBinary, rand, destNumeral)
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF
import HaskHOL.Lib.CalcNum

-- Utility Functions
lHand' :: MonadThrow m => HOLTerm -> m HOLTerm
lHand' (Binop _ l _) = return l
lHand' _ = fail' "lHand"

destAdd :: (?tmAdd :: Text, MonadThrow m) => HOLTerm -> m (HOLTerm, HOLTerm)
destAdd = B.destBinary ?tmAdd

destMul :: (?tmMul :: Text, MonadThrow m) => HOLTerm -> m (HOLTerm, HOLTerm)
destMul = B.destBinary ?tmMul

destPow :: (?tmPow :: Text, MonadThrow m) => HOLTerm -> m (HOLTerm, HOLTerm)
destPow tm =
    do (l, r) <- B.destBinary ?tmPow tm
       if isNumeral r 
          then return (l, r)
          else fail' "destPow"
        
isAdd :: (?tmAdd :: Text) => HOLTerm -> Bool
isAdd = isBinary ?tmAdd

isMul :: (?tmMul :: Text) => HOLTerm -> Bool
isMul = isBinary ?tmMul


type Normalizer cls thry =
  (?isSemiringConstant :: HOLTerm -> Bool,
   ?tmSub :: Text,
   ?tmMul :: Text,
   ?tmAdd :: Text,
   ?tmPow :: Text,
   ?tmNeg :: Text,
   ?tmZero :: PTerm thry,
   ?convSEMIRING_ADD::Conversion cls thry,
   ?convSEMIRING_POW::Conversion cls thry,
   ?convSEMIRING_MUL::Conversion cls thry,
   ?pthms::[HOLThm],
   ?ringType:: PType thry,
   ?tmOne::PTerm thry,
   ?variableOrder::HOLTerm -> HOLTerm -> Bool,
   ?nthm1 :: HOL cls thry HOLThm,
   ?nthm2 :: HOL cls thry HOLThm,
   ?destSub :: HOLTerm -> HOL cls thry (HOLTerm, HOLTerm),
   WFCtxt thry)

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

convPOWVAR_MUL :: Normalizer cls thry => Conversion cls thry
convPOWVAR_MUL = Conv $ \ tm ->
    case destMul tm of
      Right (l, r)
          | ?isSemiringConstant l && ?isSemiringConstant r ->
              runConv ?convSEMIRING_MUL tm
          | otherwise ->
              case destPow l of
                Right (lx, ln) ->
                    case destPow r of
                      Right (_, rn) ->
                          do tmX <- mkVar "x" ?ringType
                             tmP <- mkVar "p" ?ringType
                             tmQ <- mkVar "q" ?ringType
                             th1 <- primINST [(tmX, lx), (tmP, ln), (tmQ, rn)] $
                                      ?pthms !! 28
                             (tm1, tm2) <- destComb $ rand (concl th1)
                             th2 <- runConv convNUM_ADD tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                      _ ->
                          do tmX <- mkVar "x" ?ringType
                             tmQ <- mkVar "q" ?ringType
                             th1 <- primINST [(tmX, lx), (tmQ, ln)] $ 
                                      ?pthms !! 30
                             (tm1, tm2) <- destComb $ rand (concl th1)
                             th2 <- runConv convNUM_SUC tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                _ ->
                    case destPow r of
                      Right (rx, rn) ->
                          do tmX <- mkVar "x" ?ringType
                             tmQ <- mkVar "q" ?ringType
                             th1 <- primINST [(tmX, rx), (tmQ, rn)] $ 
                                      ?pthms !! 29
                             (tm1, tm2) <- destComb $ rand (concl th1)
                             th2 <- runConv convNUM_SUC tm2
                             primTRANS th1 $ ruleAP_TERM tm1 th2
                      _ -> do tmX <- mkVar "x" ?ringType
                              primINST [(tmX, l)] $ ?pthms !! 31

ruleMONOMIAL_DEONE :: Normalizer cls thry => HOLThm -> HOL cls thry HOLThm
ruleMONOMIAL_DEONE th = do
    one <- toHTm ?tmOne
    case runCatch $ destMul =<< B.rand (concl th) of
      Right (l, r)
          | l == one -> 
              do tmX <- mkVar "x" ?ringType
                 primTRANS th . primINST [(tmX, r)] $ ?pthms !! 0
          | otherwise -> return th
      _ -> return th

ruleMONOMIAL_POW :: Normalizer cls thry
                 => HOLTerm -> HOLTerm -> HOLTerm -> HOL cls thry HOLThm
ruleMONOMIAL_POW tm bod ntm =
    case bod of
      (Comb lop r)
          | ?isSemiringConstant bod -> runConv ?convSEMIRING_POW tm
          | otherwise ->
              case lop of
                (Comb op@(Const op' _) l)
                    | op' == ?tmPow && isNumeral r ->
                        do tmX <- mkVar "x" ?ringType
                           tmP <- mkVar "p" ?ringType
                           tmQ <- mkVar "q" ?ringType
                           th1 <- primINST [(tmX, l), (tmP, r), (tmQ, ntm)] $
                                    ?pthms !! 33
                           (l', r') <- destComb $ rand (concl th1)
                           th2 <- runConv convNUM_MULT r'
                           primTRANS th1 $ ruleAP_TERM l' th2
                    | op' == ?tmMul ->
                        do tmX <- mkVar "x" ?ringType
                           tmY <- mkVar "y" ?ringType
                           tmQ <- mkVar "q" ?ringType
                           th1 <- primINST [(tmX, l), (tmY, r), (tmQ, ntm)] $ 
                                    ?pthms !! 32
                           (xy, z) <- destComb $ rand (concl th1)
                           (x, y) <- destComb xy
                           thl <- ruleMONOMIAL_POW y l ntm
                           thr <- ruleMONOMIAL_POW z r ntm
                           thl' <- ruleAP_TERM x thl
                           primTRANS th1 $ primMK_COMB thl' thr
                    | otherwise -> primREFL tm
                _ -> primREFL tm
      _ -> primREFL tm

convMONOMIAL_POW :: Normalizer cls thry => Conversion cls thry
convMONOMIAL_POW = Conv $ \ tm ->
    do (lop, r) <- destComb tm
       (Const op _, l) <- destComb lop
       tmX <- mkVar "x" ?ringType
       if op /= ?tmPow || not (isNumeral r)
          then fail "convMONOMIAL_POW"
          else case r of
                 ZERON -> primINST [(tmX, l)] $ ?pthms !! 34
                 ONEN -> primINST [(tmX, l)] $ ?pthms !! 35
                 _ -> do th <- ruleMONOMIAL_POW tm l r
                         ruleMONOMIAL_DEONE th

ruleMONOMIAL_MUL :: forall cls thry. Normalizer cls thry
                 => HOLTerm -> HOLTerm -> HOLTerm -> HOL cls thry HOLThm
ruleMONOMIAL_MUL tm l r = do
    one <- toHTm ?tmOne
    let vorder = vorder' one
    case destMul l of
      Right (lx, ly) ->
        case destMul r of
          Right (rx, ry) ->
            do vl <- powvar lx
               vr <- powvar rx
               let ord = vorder vl vr
               if ord == EQ
                  then do tmLX <- mkVar "lx" ?ringType
                          tmLY <- mkVar "ly" ?ringType
                          tmRX <- mkVar "rx" ?ringType
                          tmRY <- mkVar "ry" ?ringType
                          th1 <- primINST [ (tmLX, lx), (tmLY, ly)
                                          , (tmRX, rx), (tmRY, ry) 
                                          ] $ ?pthms !! 14
                          (tm1, tm2) <- destComb $ rand (concl th1)
                          (tm3, tm4) <- destComb tm1
                          th1_5 <- runConv convPOWVAR_MUL tm4
                          th2 <- ruleAP_THM (ruleAP_TERM tm3 th1_5) tm2
                          th3 <- primTRANS th1 th2
                          (tm5, tm6) <- destComb $ rand (concl th3)
                          (tm7, tm8) <- destComb tm6
                          tm9 <- rand tm7
                          th4 <- ruleMONOMIAL_MUL tm6 tm9 tm8
                          primTRANS th3 $ ruleAP_TERM tm5 th4
                  else let th0 = (!!) ?pthms $ if ord == LT then 15 else 16 in
                         do tmLX <- mkVar "lx" ?ringType
                            tmLY <- mkVar "ly" ?ringType
                            tmRX <- mkVar "rx" ?ringType
                            tmRY <- mkVar "ry" ?ringType
                            th1 <- primINST [ (tmLX, lx), (tmLY, ly)
                                            , (tmRX, rx), (tmRY, ry) ] th0
                            (tm1, tm2) <- destComb $ rand (concl th1)
                            (tm3, tm4) <- destComb tm2
                            tm5 <- rand tm3
                            th2 <- ruleMONOMIAL_MUL tm2 tm5 tm4
                            primTRANS th1 $ ruleAP_TERM tm1 th2
          _ ->
            do vl <- powvar lx
               vr <- powvar r
               case vorder vl vr of
                 EQ ->
                     do tmLX <- mkVar "lx" ?ringType
                        tmLY <- mkVar "ly" ?ringType
                        tmRX <- mkVar "rx" ?ringType
                        th1 <- primINST [ (tmLX, lx), (tmLY, ly)
                                        , (tmRX, r) ] $ ?pthms !! 17
                        (tm1, tm2) <- destComb $ rand (concl th1)
                        (tm3, tm4) <- destComb tm1
                        th1_5 <-  runConv convPOWVAR_MUL tm4
                        th2 <- ruleAP_THM (ruleAP_TERM tm3 th1_5) tm2
                        primTRANS th1 th2
                 LT ->
                     do tmLX <- mkVar "lx" ?ringType
                        tmLY <- mkVar "ly" ?ringType
                        tmRX <- mkVar "rx" ?ringType
                        th1 <- primINST [ (tmLX, lx), (tmLY, ly)
                                        , (tmRX, r) ] $ ?pthms !! 18
                        (tm1, tm2) <- destComb $ rand (concl th1)
                        (tm3, tm4) <- destComb tm2
                        tm5 <- rand tm3
                        th2 <- ruleMONOMIAL_MUL tm2 tm5 tm4
                        primTRANS th1 $ ruleAP_TERM tm1 th2
                 _ -> 
                   do tmLX <- mkVar "lx" ?ringType
                      tmRX <- mkVar "rx" ?ringType
                      primINST [(tmLX, l), (tmRX, r)] $ ?pthms !! 19
      _ ->
        case destMul r of
          Right (rx, ry) ->
            do vl <- powvar l
               vr <- powvar rx
               case vorder vl vr of
                 EQ ->
                     do tmLX <- mkVar "lx" ?ringType
                        tmRX <- mkVar "rx" ?ringType
                        tmRY <- mkVar "ry" ?ringType
                        th1 <- primINST [ (tmLX, l), (tmRX, rx), (tmRY, ry) ] $ 
                                 ?pthms !! 20
                        (tm1, tm2) <- destComb $ rand (concl th1)
                        (tm3, tm4) <- destComb tm1
                        th2 <- runConv convPOWVAR_MUL tm4
                        primTRANS th1 $ ruleAP_THM (ruleAP_TERM tm3 th2) tm2
                 GT ->
                     do tmLX <- mkVar "lx" ?ringType
                        tmRX <- mkVar "rx" ?ringType
                        tmRY <- mkVar "ry" ?ringType
                        th1 <- primINST [ (tmLX, l), (tmRX, rx)
                                        , (tmRY, ry) ] $ ?pthms !! 21
                        (tm1, tm2) <- destComb $ rand (concl th1)
                        (tm3, tm4) <- destComb tm2
                        tm5 <- rand tm3
                        th2 <- ruleMONOMIAL_MUL tm2 tm5 tm4
                        primTRANS th1 $ ruleAP_TERM tm1 th2
                 _ -> primREFL tm
          _ ->
            do vl <- powvar l
               vr <- powvar r
               case vorder vl vr of
                 EQ -> runConv convPOWVAR_MUL tm
                 GT -> do tmLX <- mkVar "lx" ?ringType
                          tmRX <- mkVar "rx" ?ringType
                          primINST [(tmLX, l), (tmRX, r)] $ ?pthms !! 19
                 _ -> primREFL tm
  where powvar :: HOLTerm -> HOL cls thry HOLTerm
        powvar tm
            | ?isSemiringConstant tm = toHTm ?tmOne
            | otherwise = 
                case tm of
                  (Comb lop r) ->
                      case lop of
                        (Comb (Const op _) l)
                            | op == ?tmPow && isNumeral r -> return l
                            | otherwise -> fail "powvar"
                        _ -> return tm
                  _ -> return tm

        vorder' :: HOLTerm -> HOLTerm -> HOLTerm -> Ordering
        vorder' one x y
            | x == y = EQ
            | x == one = LT
            | y == one = GT
            | ?variableOrder x y = LT
            | otherwise = GT

convMONOMIAL_MUL :: Normalizer cls thry => Conversion cls thry
convMONOMIAL_MUL = Conv $ \ tm ->
    case destMul tm of
      Right (l, r) ->
          do th <- ruleMONOMIAL_MUL tm l r
             ruleMONOMIAL_DEONE th
      _ -> fail "convMONOMIAL_MUL"


convPOLYNOMIAL_MONOMIAL_MUL :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_MONOMIAL_MUL = Conv $ \ tm ->
    case destMul tm of
      Right (l, r) ->
        case destAdd r of
          Right (y, z) ->
            do tmX <- mkVar "x" ?ringType
               tmY <- mkVar "y" ?ringType
               tmZ <- mkVar "z" ?ringType
               th1 <- primINST [(tmX, l), (tmY, y), (tmZ, z)] $ ?pthms !! 36
               (tm1, tm2) <- destComb $ rand (concl th1)
               (tm3, tm4) <- destComb tm1
               thl <- runConv convMONOMIAL_MUL tm4
               thr <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm2
               th2 <- primMK_COMB (ruleAP_TERM tm3 thl) thr
               primTRANS th1 th2
          _ -> runConv convMONOMIAL_MUL tm
      _ -> fail "convPOLYNOMIAL_MONOMIAL_MUL"


convMONOMIAL_ADD :: Normalizer cls thry => Conversion cls thry
convMONOMIAL_ADD = Conv $ \ tm ->
    case destAdd tm of
      Right (l, r)
          | ?isSemiringConstant l && ?isSemiringConstant r ->
              runConv ?convSEMIRING_ADD tm
          | otherwise ->
              do th1 <- let ll' = lHand' l
                            rl' = lHand' r in
                          if isMul l && ?isSemiringConstant (try' ll')
                          then if isMul r && ?isSemiringConstant (try' rl')
                               then do tmA <- mkVar "a" ?ringType
                                       tmB <- mkVar "b" ?ringType
                                       tmM <- mkVar "m" ?ringType
                                       primINST [ (tmA, try' ll')
                                                , (tmB, try' rl')
                                                , (tmM, try' $ B.rand r) 
                                                ] $ ?pthms !! 1
                               else do tmA <- mkVar "a" ?ringType
                                       tmM <- mkVar "m" ?ringType
                                       primINST [(tmA, try' ll'), (tmM, r)] $ 
                                         ?pthms !! 2
                          else if isMul r && ?isSemiringConstant (try' rl')
                               then do tmA <- mkVar "a" ?ringType
                                       tmM <- mkVar "m" ?ringType
                                       primINST [(tmA, try' rl'), (tmM, l)] $
                                         ?pthms !! 3
                               else do tmR <- mkVar "r" ?ringType
                                       primINST [(tmR, r)] $ ?pthms !! 4
                 (tm1, tm2) <- destComb $ rand (concl th1)
                 (tm3, tm4) <- destComb tm1
                 th1_5 <- runConv ?convSEMIRING_ADD tm4
                 th2 <- ruleAP_TERM tm3 th1_5
                 th3 <- primTRANS th1 $ ruleAP_THM th2 tm2
                 tm5 <- rand $ concl th3
                 tm6 <- lHand tm5
                 one <- toHTm ?tmOne
                 if tm6 == one
                    then do tmM <- mkVar "m" ?ringType
                            primTRANS th3 (primINST [(tmM, r)] $ ?pthms !! 5)
                    else ruleMONOMIAL_DEONE th3

ruleDEZERO :: Normalizer cls thry => HOLThm -> HOL cls thry HOLThm
ruleDEZERO th =
  do tm <- rand $ concl th
     if not (isAdd tm) 
        then return th
        else do (lop, r) <- destComb tm
                l <- rand lop
                zero <- toHTm ?tmZero
                if l == zero 
                   then do tmA <- mkVar "a" ?ringType
                           primTRANS th . primINST [(tmA, r)] $ ?pthms !! 6
                   else if r == zero
                        then do tmA <- mkVar "a" ?ringType
                                primTRANS th . primINST [(tmA, l)] $ ?pthms !! 7
                        else return th


convPOLYNOMIAL_ADD :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_ADD = Conv $ \ tm -> do
   zero <- toHTm ?tmZero
   case destAdd tm of
     Right (l, r)
      | l == zero -> 
          do tmA <- mkVar "a" ?ringType
             primINST [(tmA, r)] $ ?pthms !! 6
      | r == zero -> 
          do tmA <- mkVar "a" ?ringType
             primINST [(tmA, l)] $ ?pthms !! 7
      | otherwise ->
          case destAdd l of
            Right (a, b) ->
              case destAdd r of
                Right (c, d) ->
                  case morder a c of
                    EQ ->
                      do tmA <- mkVar "a" ?ringType
                         tmB <- mkVar "b" ?ringType
                         tmC <- mkVar "c" ?ringType
                         tmD <- mkVar "d" ?ringType
                         th1 <- primINST [ (tmA, a), (tmB, b)
                                         , (tmC, c), (tmD, d) ] $ ?pthms !! 22
                         (tm1, tm2) <- destComb $ rand (concl th1)
                         (tm3, tm4) <- destComb tm1
                         th1_5 <- runConv convMONOMIAL_ADD tm4  
                         th2 <- ruleAP_TERM tm3 th1_5
                         th3 <- runConv convPOLYNOMIAL_ADD tm2 
                         ruleDEZERO =<< primTRANS th1 =<< primMK_COMB th2 th3
                    GT ->
                      do tmA <- mkVar "a" ?ringType
                         tmB <- mkVar "b" ?ringType
                         tmC <- mkVar "c" ?ringType
                         th1 <- primINST [ (tmA, a), (tmB, b)
                                         , (tmC, r) ] $ ?pthms !! 23
                         (tm1, tm2) <- destComb =<< rand (concl th1)
                         th2 <- runConv convPOLYNOMIAL_ADD tm2
                         ruleDEZERO =<< primTRANS th1 =<< ruleAP_TERM tm1 th2

                    _ ->
                      do tmA <- mkVar "a" ?ringType
                         tmC <- mkVar "c" ?ringType
                         tmD <- mkVar "d" ?ringType
                         th1 <- primINST [ (tmA, l), (tmC, c)
                                         , (tmD, d) ] $ ?pthms !! 24
                         (tm1, tm2) <- destComb =<< rand (concl th1)
                         th2 <- runConv convPOLYNOMIAL_ADD tm2
                         ruleDEZERO =<< primTRANS th1 =<< ruleAP_TERM tm1 th2
                _ ->
                  case morder a r of
                    EQ ->
                      do tmA <- mkVar "a" ?ringType
                         tmB <- mkVar "b" ?ringType
                         tmC <- mkVar "c" ?ringType
                         th1 <- primINST [ (tmA, a), (tmB, b)
                                         , (tmC, r) ] $ ?pthms !! 25
                         (tm1, tm2) <- destComb $ rand (concl th1)
                         (tm3, tm4) <- destComb tm1
                         thl <- runConv convMONOMIAL_ADD tm4
                         th2 <- ruleAP_THM (ruleAP_TERM tm3 thl) tm2
                         ruleDEZERO =<< primTRANS th1 th2
                    GT ->
                      do tmA <- mkVar "a" ?ringType
                         tmB <- mkVar "b" ?ringType
                         tmC <- mkVar "c" ?ringType
                         th1 <- primINST [ (tmA, a), (tmB, b)
                                         , (tmC, r) ] $ ?pthms !! 23
                         (tm1, tm2) <- destComb $ rand (concl th1)
                         th <- runConv convPOLYNOMIAL_ADD tm2
                         ruleDEZERO =<< primTRANS th1 =<< ruleAP_TERM tm1 th
                    _ ->
                      do tmA <- mkVar "a" ?ringType
                         tmC <- mkVar "c" ?ringType
                         ruleDEZERO =<< 
                           primINST [(tmA, l), (tmC, r)] (?pthms !! 26)
            _ ->
              case destAdd r of
                Right (c, d) ->
                  case morder l c of
                    EQ ->
                      do tmA <- mkVar "a" ?ringType
                         tmC <- mkVar "c" ?ringType
                         tmD <- mkVar "d" ?ringType
                         th1 <- primINST [ (tmA, l), (tmC, c)
                                         , (tmD, d) ] $ ?pthms !! 27
                         (tm1, tm2) <- destComb $ rand (concl th1)
                         (tm3, tm4) <- destComb tm1
                         th1_5 <- runConv convMONOMIAL_ADD tm4
                         th2 <- ruleAP_THM (ruleAP_TERM tm3 th1_5) tm2
                         ruleDEZERO =<< primTRANS th1 th2
                    GT -> 
                      primREFL tm
                    _ ->
                      do tmA <- mkVar "a" ?ringType
                         tmC <- mkVar "c" ?ringType
                         tmD <- mkVar "d" ?ringType
                         th1 <- primINST [ (tmA, l), (tmC, c)
                                         , (tmD, d) ] $ ?pthms !! 24
                         (tm1, tm2) <- destComb $ rand (concl th1)
                         th2 <- runConv convPOLYNOMIAL_ADD tm2
                         ruleDEZERO =<< primTRANS th1 =<< ruleAP_TERM tm1 th2
                _ -> 
                  case morder l r of
                    EQ -> runConv convMONOMIAL_ADD tm
                    GT -> ruleDEZERO =<< primREFL tm
                    _ -> 
                      do tmA <- mkVar "a" ?ringType
                         tmC <- mkVar "c" ?ringType
                         ruleDEZERO =<< 
                           primINST [(tmA, l), (tmC, r)] (?pthms !! 26)
     _ -> fail "convPOLYNOMIAL_ADD"               


rulePMUL :: Normalizer cls thry => HOLTerm -> HOL cls thry HOLThm
rulePMUL tm =
    do (l, r) <- eitherToFail $ destMul tm
       tmA <- mkVar "a" ?ringType
       tmB <- mkVar "b" ?ringType
       if not (isAdd l) 
          then runConv convPOLYNOMIAL_MONOMIAL_MUL tm
          else if not (isAdd r)
               then do th1 <- primINST [(tmA, l), (tmB, r)] $ ?pthms !! 8
                       th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL $ 
                                rand (concl th1)
                       primTRANS th1 th2
               else do (a, b) <- eitherToFail $ destAdd l
                       tmC <- mkVar "c" ?ringType
                       th1 <- primINST [(tmA, a), (tmB, b), (tmC, r)] $ 
                                ?pthms !! 9
                       (tm1, tm2) <- destComb $ rand (concl th1)
                       (tm3, tm4) <- destComb tm1
                       th1_5 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm4
                       th2 <- ruleAP_TERM tm3 th1_5
                       th2_5 <- rulePMUL tm2
                       th3 <- primTRANS th1 $ primMK_COMB th2 th2_5
                       th4 <- runConv convPOLYNOMIAL_ADD $ rand (concl th3)
                       primTRANS th3 th4

convPOLYNOMIAL_MUL :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_MUL = Conv $ \ tm ->
    do (l, r) <- eitherToFail $ destMul tm
       tmA <- mkVar "a" ?ringType
       zero <- toHTm ?tmZero
       one <- toHTm ?tmOne
       if l == zero 
          then primINST [(tmA, r)] $ ?pthms !! 10
          else if r == zero then primINST [(tmA, l)] $ ?pthms !! 11
          else if l == one then primINST [(tmA, r)] $ ?pthms !! 12
          else if r == one then primINST [(tmA, l)] $ ?pthms !! 13
          else rulePMUL tm

rulePPOW :: Normalizer cls thry => HOLTerm -> HOL cls thry HOLThm
rulePPOW tm =
    do (l, n) <- eitherToFail $ destPow tm
       tmX <- mkVar "x" ?ringType
       case n of
         ZERON -> primINST [(tmX, l)] $ ?pthms !! 34
         ONEN -> primINST [(tmX, l)] $ ?pthms !! 35
         _ ->  do th1 <- runConv convNUM n
                  qtm' <- rand $ rand (concl th1)
                  tmQ <- mkVar "q" ?ringType
                  th2 <- primINST [(tmX, l), (tmQ, qtm')] $ ?pthms !! 37
                  (tm1, tm2) <- destComb $ rand (concl th2)
                  thr <- rulePPOW tm2
                  th3 <- primTRANS th2 $ ruleAP_TERM tm1 thr
                  tm' <- rator tm
                  th4 <- primTRANS (ruleAP_TERM tm' th1) th3
                  th5 <- runConv convPOLYNOMIAL_MUL $ rand (concl th4)
                  primTRANS th4 th5

convPOLYNOMIAL_POW :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_POW = Conv $ \ tm ->
    do l <- lHand tm
       if isAdd l
          then rulePPOW tm
          else runConv convMONOMIAL_POW tm

convPOLYNOMIAL_NEG :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_NEG = Conv $ \ tm ->
    do (Const l _, r) <- destComb tm
       if l /= ?tmNeg then fail "convPOLYNOMIAL_NEG"
          else do tmX <- mkVar "x" ?ringType
                  th1 <- primINST [(tmX, r)] ?nthm1
                  th2 <- runConv convPOLYNOMIAL_MONOMIAL_MUL $ rand (concl th1)
                  primTRANS th1 th2

convPOLYNOMIAL_SUB :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL_SUB = Conv $ \ tm ->
    do (l, r) <- ?destSub tm
       tmX <- mkVar "x" ?ringType
       tmY <- mkVar "y" ?ringType
       th1 <- primINST [(tmX, l), (tmY, r)] ?nthm2
       (tm1, tm2) <- destComb $ rand (concl th1)
       thr1 <- runConv convPOLYNOMIAL_MONOMIAL_MUL tm2
       th2 <- ruleAP_TERM tm1 thr1
       thr2 <- runConv convPOLYNOMIAL_ADD $ rand (concl th2)
       primTRANS th1 $ primTRANS th2 thr2

convPOLYNOMIAL :: Normalizer cls thry => Conversion cls thry
convPOLYNOMIAL = Conv $ \ tm ->
    if ?isSemiringConstant tm then primREFL tm
    else case tm of
           (Comb lop@(Const lop' _) r)
               | lop' == ?tmNeg ->
                   do th0_5 <- runConv convPOLYNOMIAL r
                      th1 <- ruleAP_TERM lop th0_5
                      th2 <- runConv convPOLYNOMIAL_NEG $ rand (concl th1)
                      primTRANS th1 th2
               | otherwise -> primREFL tm
           (Comb lop r) ->
               case lop of
                 (Comb op@(Const op' _) l)
                     | op' == ?tmPow && isNumeral r ->
                         do th0_5 <- runConv convPOLYNOMIAL l
                            th1 <- ruleAP_THM (ruleAP_TERM op th0_5) r
                            th2 <- runConv convPOLYNOMIAL_POW $ rand (concl th1)
                            primTRANS th1 th2
                     | op' == ?tmAdd || op' == ?tmMul || op' == ?tmSub ->
                         do thl <- runConv convPOLYNOMIAL l
                            thr <- runConv convPOLYNOMIAL r
                            th1 <- primMK_COMB (ruleAP_TERM op thl) thr
                            let fn 
                                    | op' == ?tmAdd = convPOLYNOMIAL_ADD
                                    | op' == ?tmMul = convPOLYNOMIAL_MUL
                                    | otherwise = convPOLYNOMIAL_SUB
                            th2 <- runConv fn $ rand (concl th1)
                            primTRANS th1 th2
                     | otherwise -> primREFL tm
                 _ -> primREFL tm
           _ -> primREFL tm


convSEMIRING_NORMALIZERS :: Normalizer cls thry
                         => ( Conversion cls thry, Conversion cls thry
                            , Conversion cls thry, Conversion cls thry
                            , Conversion cls thry, Conversion cls thry )
convSEMIRING_NORMALIZERS = 
    ( convPOLYNOMIAL_NEG, convPOLYNOMIAL_ADD, convPOLYNOMIAL_SUB
    , convPOLYNOMIAL_MUL, convPOLYNOMIAL_POW, convPOLYNOMIAL )

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
    do pthms <- ruleCONJUNCTS $ ruleMATCH_MP semiring_pth convNUM_NORMALIZE_sth
       let ?pthms = pthms
       let (_, _, _, _, _, conv) = convSEMIRING_NORMALIZERS
       runConv conv tm
  where ?isSemiringConstant = isNumeral
        ?tmSub = "T"
        ?tmMul = "*"
        ?tmAdd = "+"
        ?tmPow = "EXP"
        ?tmNeg = "T"
        ?tmZero = [wf| 0 |]
        ?convSEMIRING_ADD = convNUM_ADD
        ?convSEMIRING_POW = convNUM_EXP
        ?convSEMIRING_MUL = convNUM_MULT
        ?ringType = [wf| :num |]
        ?tmOne = [wf| 1 |]
        ?variableOrder = (<)
        ?nthm1 = thmTRUTH
        ?nthm2 = thmTRUTH
        ?destSub = \ t -> return (t, t)
  
morder :: (?isSemiringConstant :: HOLTerm -> Bool,
           ?variableOrder :: HOLTerm -> HOLTerm -> Bool,
           ?tmMul :: Text,
           ?tmPow :: Text)
       => HOLTerm -> HOLTerm -> Ordering
morder tm1 tm2 =
    let vdegs1 = try' . mapM destVarpow $ powervars tm1
        vdegs2 = try' . mapM destVarpow $ powervars tm2
        deg1 = foldr ((+) . snd) 0 vdegs1
        deg2 = foldr ((+) . snd) 0 vdegs2 in
      if deg1 < deg2 then LT
      else if deg1 > deg2 then GT
      else lexorder vdegs1 vdegs2
  where destVarpow :: MonadThrow m => HOLTerm -> m (HOLTerm, Integer)
        destVarpow tm =
            case destPow tm of
              Right (x, n) ->
                  do n' <- B.destNumeral n
                     return (x, n')
              _ -> return (tm, if ?isSemiringConstant tm then 0 else 1)

        powervars :: HOLTerm -> [HOLTerm]
        powervars tm =
            let ptms = stripList destMul tm in
              if ?isSemiringConstant $ head ptms
              then tail ptms
              else ptms

        lexorder :: [(HOLTerm, Integer)] -> [(HOLTerm, Integer)] -> Ordering
        lexorder [] [] = EQ
        lexorder _ [] = LT
        lexorder [] _ = GT
        lexorder ((x1, n1):vs1) ((x2, n2):vs2)
            | ?variableOrder x1 x2 = GT
            | ?variableOrder x2 x1 = LT
            | n1 < n2 = LT
            | n2 < n1 = GT
            | otherwise = lexorder vs1 vs2
                          
