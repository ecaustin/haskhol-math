module HaskHOL.Lib.IndTypes.A.Pre where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.WF
import HaskHOL.Lib.WF.Context

thmINJ_INVERSE2 :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
thmINJ_INVERSE2 = cacheProof "thmINJ_INVERSE2" ctxtWF $
    prove [str| !P:A->B->C.
                (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) <=> (x1 = x2) /\ (y1 = y2))
                ==> ?X Y. !x y. (X(P x y) = x) /\ (Y(P x y) = y) |] $
      tacGEN `_THEN` tacDISCH `_THEN`
      tacEXISTS [str| \z:C. @x:A. ?y:B. P x y = z |] `_THEN`
      tacEXISTS [str| \z:C. @y:B. ?x:A. P x y = z |] `_THEN`
      _REPEAT tacGEN `_THEN` tacASM_REWRITE [thmBETA] `_THEN`
      tacCONJ `_THEN` tacMATCH_MP thmSELECT_UNIQUE `_THEN` tacGEN `_THEN`
      tacBETA `_THEN` tacEQ `_THEN` tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
      (\ g@(Goal _ w) -> tacEXISTS 
                          (rand =<< liftM snd (destExists w)) g) `_THEN` tacREFL

thmNUMPAIR_INJ_LEMMA :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
thmNUMPAIR_INJ_LEMMA = cacheProof "thmNUMPAIR_INJ_LEMMA" ctxtWF $
    do tm <- toHTm "EVEN"
       prove "!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)" $
         tacREWRITE [defNUMPAIR] `_THEN` 
         _REPEAT (tacINDUCT `_THEN` tacGEN) `_THEN`
         tacASM_REWRITE [ defEXP, ruleGSYM thmMULT_ASSOC, thmARITH
                        , thmEQ_MULT_LCANCEL
                        , thmNOT_SUC, ruleGSYM thmNOT_SUC, thmSUC_INJ ] `_THEN`
         _DISCH_THEN (tacMP <#< ruleAP_TERM tm) `_THEN`
         tacREWRITE [thmEVEN_MULT, thmEVEN_ADD, thmARITH]

thmNUMSUM_INJ :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
thmNUMSUM_INJ = cacheProof "thmNUMSUM_INJ" ctxtWF $
    do tm <- toHTm "EVEN"
       prove [str| !b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> 
                                 (b1 = b2) /\ (x1 = x2) |] $
         _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
         tacASM_REWRITE_NIL `_THEN`
         _POP_ASSUM (tacMP . ruleREWRITE [defNUMSUM]) `_THEN`
         _DISCH_THEN (\ th -> tacMP th `_THEN` 
                              tacMP (ruleAP_TERM tm th)) `_THEN`
         _REPEAT tacCOND_CASES `_THEN` 
         tacREWRITE [defEVEN, thmEVEN_DOUBLE] `_THEN`
         tacREWRITE [thmSUC_INJ, thmEQ_MULT_LCANCEL, thmARITH]
