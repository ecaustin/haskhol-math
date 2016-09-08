module HaskHOL.Lib.Grobner
    ( convNUM_SIMPLIFY
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Normalizer
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.WF
import HaskHOL.Lib.Arith

convNUM_SIMPLIFY :: ArithCtxt thry => Conversion cls thry
convNUM_SIMPLIFY =
    convNUM_REDUCE `_THEN` convCONDS_CELIM `_THEN` convNNF `_THEN`
    convNUM_MULTIPLY `_THEN` convNUM_REDUCE `_THEN`
    convGEN_REWRITE convONCE_DEPTH [pth]
  where convNUM_MULTIPLY :: ArithCtxt thry => Bool -> Conversion cls thry
        convNUM_MULTIPLY pos = Conv $ \ tm ->
          if isForall tm || isExists tm || isUExists tm
               then runConv (convBINDER (convNUM_MULTIPLY pos)) tm
          else if isImp tm && containsQuantifier tm
               then runConv (convCOMB2 (convRAND (convNUM_MULTIPLY (not pos)))
                                       (convNUM_MULTIPLY pos)) tm
          else if (isConj tm || isDisj tm || isIff tm) &&
                  containsQuantifier tm
               then runConv (convBINOP (convNUM_MULTIPLY pos)) tm
          else if (isNeg tm && not pos && containsQuantifier tm)
               then runConv (convRAND (convNUM_MULTIPLY (not pos))) tm
          else do tmA <- toHTm [arith| a:num |]
                  tmB <- toHTm [arith| b:num |]
                  tmM <- toHTm [arith| m:num |]
                  tmN <- toHTm [arith| n:num |]
                  tmP <- toHTm [arith| P:num->bool |]
                  tmQ <- toHTm [arith| P:num->num->bool |]
                  tmDiv <- toHTm [arith| (DIV):num->num->num |]
                  tmMod <- toHTm [arith| (MOD):num->num->num |]
                  ((do t <- findTerm (\ t -> isPre t && freeIn t tm) tm
                       ty <- typeOf t
                       v <- genVar ty
                       p <- mkAbs v $ subst [(t, v)] tm
                       th0 <- if pos then thmPRE_ELIM'' else thmPRE_ELIM'
                       t' <- rand t
                       th1 <- primINST [(tmP, p), (tmN, t')] th0
                       th2 <- ruleCONV (convCOMB2 (convRAND convBETA)
                                (convBINDER (convRAND convBETA))) th1
                       ruleCONV (convRAND (convNUM_MULTIPLY pos)) th2) <|>
                   (do t <- findTerm (\ t -> isSub t && freeIn t tm) tm
                       ty <- typeOf t
                       v <- genVar ty
                       p <- mkAbs v $ subst [(t, v)] tm
                       th0 <- if pos then thmSUB_ELIM'' else thmSUB_ELIM'
                       t' <- lHand t
                       t'' <- rand t
                       th1 <- primINST [(tmP, p), (tmA, t'), (tmB, t'')] th0
                       th2 <- ruleCONV (convCOMB2 (convRAND convBETA)
                                (convBINDER (convRAND convBETA))) th1
                       ruleCONV (convRAND (convNUM_MULTIPLY pos)) th2) <|>
                   (do t <- findTerm (\ t -> isDivmod t && freeIn t tm) tm
                       x <- lHand t
                       y <- rand t
                       dtm <- mkComb (mkComb tmDiv x) y
                       mtm <- mkComb (mkComb tmMod x) y
                       vd <- genVar $ typeOf dtm
                       vm <- genVar $ typeOf mtm
                       p <- listMkAbs [vd, vm] $ subst [(dtm, vd), (mtm, vm)] tm
                       th0 <- if pos then thmDIVMOD_ELIM'' else thmDIVMOD_ELIM'
                       th1 <- primINST [(tmQ, p), (tmM, x), (tmN, y)] th0
                       th2 <- ruleCONV (convCOMB2 (convRAND convBETA2)
                                (funpow 2 convBINDER (convRAND convBETA2))) th1
                       ruleCONV (convRAND (convNUM_MULTIPLY pos)) th2) <|>
                   (primREFL tm))

        isPre :: HOLTerm -> Bool
        isPre (Comb (Const "PRE" _) _) = True
        isPre _ = False

        isSub :: HOLTerm -> Bool
        isSub = isBinary "-"

        isDivmod :: HOLTerm -> Bool
        isDivmod tm =
            isBinary "DIV" tm || isBinary "MOD" tm

        containsQuantifier :: HOLTerm -> Bool
        containsQuantifier =
          test' . (findTerm (\ t -> isForall t || isExists t || isUExists t))

        convBETA2 :: Conversion cls thry
        convBETA2 = convRATOR convBETA `_THEN` convBETA

        thmPRE_ELIM'' :: ArithCtxt thry => HOL cls thry HOLThm
        thmPRE_ELIM'' = cacheProof "thmPRE_ELIM''" ctxtArith $
            ruleCONV (convRAND convNNF) thmPRE_ELIM

        thmSUB_ELIM'' :: ArithCtxt thry => HOL cls thry HOLThm
        thmSUB_ELIM'' = cacheProof "thmSUB_ELIM''" ctxtArith $
            ruleCONV (convRAND convNNF) thmSUB_ELIM

        thmDIVMOD_ELIM'' :: ArithCtxt thry => HOL cls thry HOLThm
        thmDIVMOD_ELIM'' = cacheProof "thmDIVMOD_ELIM''" ctxtArith $
            ruleCONV (convRAND convNNF) thmDIVMOD_ELIM

        pth :: ArithCtxt thry => HOL cls thry HOLThm
        pth = cacheProof "convNUM_SIMPLIFY_pth" ctxtArith .
            prove [txt| (EVEN(x) <=> (!y. ~(x = SUC(2 * y)))) /\
                        (ODD(x) <=> (!y. ~(x = 2 * y))) /\
                        (~EVEN(x) <=> (!y. ~(x = 2 * y))) /\
                        (~ODD(x) <=> (!y. ~(x = SUC(2 * y)))) |] $
              tacREWRITE [ ruleGSYM thmNOT_EXISTS, ruleGSYM thmEVEN_EXISTS
                         , ruleGSYM thmODD_EXISTS] `_THEN`
              tacREWRITE [thmNOT_EVEN, thmNOT_ODD]
