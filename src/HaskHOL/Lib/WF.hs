{-|
  Module:    HaskHOL.Lib.WF
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.WF
    ( WFCtxt
    , ctxtWF
    , wf
    , defWF
    , defMEASURE
    , defNUMPAIR
    , defNUMSUM
    , thmWF_LEX_DEPENDENT
    , thmWF_IND
    , thmWF_LEX
    , thmWF_MEASURE_GEN
    , wfNUM
    , thmWF_MEASURE
    , thmMEASURE_LE
    , thmWF_FALSE
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Arith

import HaskHOL.Lib.WF.Context
import HaskHOL.Lib.WF.PQ

defWF :: WFCtxt thry => HOL cls thry HOLThm
defWF = cacheProof "defWF" ctxtWF $ getDefinition "WF"

defMEASURE :: WFCtxt thry => HOL cls thry HOLThm
defMEASURE = cacheProof "defMEASURE" ctxtWF $ getDefinition "MEASURE"

defNUMPAIR :: WFCtxt thry => HOL cls thry HOLThm
defNUMPAIR = cacheProof "defNUMPAIR" ctxtWF $ getDefinition "NUMPAIR"

defNUMSUM :: WFCtxt thry => HOL cls thry HOLThm
defNUMSUM = cacheProof "defNUMSUM" ctxtWF $ getDefinition "NUMSUM"

thmWF_LEX_DEPENDENT :: WFCtxt thry => HOL cls thry HOLThm
thmWF_LEX_DEPENDENT = cacheProof "thmWF_LEX_DEPENDENT" ctxtWF .
  prove [str| !R:A->A->bool S:A->B->B->bool. WF(R) /\ (!a. WF(S a))
              ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S r1 s1 s2) |] $
    _REPEAT tacGEN `_THEN` tacREWRITE [defWF] `_THEN` tacSTRIP `_THEN`
    tacX_GEN "P:A#B->bool" `_THEN` tacREWRITE [thmLEFT_IMP_EXISTS] `_THEN`
    tacGEN_REWRITE id [thmFORALL_PAIR] `_THEN` 
    _MAP_EVERY tacX_GEN ["a0:A", "b0:B"] `_THEN` tacDISCH `_THEN`
    _FIRST_X_ASSUM (tacMP . ruleSPEC [str| \a:A. ?b:B. P(a,b) |]) `_THEN`
    tacREWRITE [thmLEFT_IMP_EXISTS] `_THEN`
    _DISCH_THEN (tacMP . ruleSPECL ["a0:A", "b0:B"]) `_THEN` 
    tacASM_REWRITE_NIL `_THEN`
    _DISCH_THEN (_X_CHOOSE_THEN "a:A" (_CONJUNCTS_THEN2 tacMP tacASSUME)) 
    `_THEN` _DISCH_THEN (tacX_CHOOSE "b1:B") `_THEN`
    _FIRST_X_ASSUM (tacMP . ruleSPECL ["a:A", [str| \b. (P:A#B->bool) (a,b) |]])
    `_THEN` tacREWRITE [thmLEFT_IMP_EXISTS] `_THEN`
    _DISCH_THEN (tacMP . ruleSPEC "b1:B") `_THEN` tacASM_REWRITE_NIL `_THEN`
    _DISCH_THEN (_X_CHOOSE_THEN "b:B" (_CONJUNCTS_THEN2 tacMP tacASSUME)) 
    `_THEN` tacDISCH `_THEN` tacEXISTS "(a:A, b:B)" `_THEN` tacASM_REWRITE_NIL 
    `_THEN` tacREWRITE [thmFORALL_PAIR] `_THEN` tacASM_MESON_NIL

thmWF_IND ::  WFCtxt thry => HOL cls thry HOLThm
thmWF_IND = cacheProof "thmWF_IND" ctxtWF .
    prove [str| WF(<<) <=> !P:A->bool. 
                (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x) |] $
      tacREWRITE [defWF] `_THEN` tacEQ `_THEN` tacDISCH `_THEN` tacGEN `_THEN`
      _POP_ASSUM (tacMP . ruleSPEC [str| \x:A. ~P(x) |]) `_THEN`
      tacREWRITE_NIL `_THEN` tacMESON_NIL

thmWF_MEASURE_GEN :: WFCtxt thry => HOL cls thry HOLThm
thmWF_MEASURE_GEN = cacheProof "thmWF_MEASURE_GEN" ctxtWF .
    prove [str| !m:A->B. WF(<<) ==> WF(\x x'. m x << m x') |] $
      tacGEN `_THEN` tacREWRITE [thmWF_IND] `_THEN` _REPEAT tacSTRIP `_THEN`
      _FIRST_ASSUM (tacMP . ruleSPEC [str| \y:B. !x:A. (m(x) = y) ==> P x |]) 
      `_THEN` tacUNDISCH "!x. (!y. (m:A->B) y << m x ==> P y) ==> P x" `_THEN`
      tacREWRITE_NIL `_THEN` tacMESON_NIL

wfNUM :: WFCtxt thry => HOL cls thry HOLThm
wfNUM = cacheProof "wfNUM" ctxtWF . 
    prove "WF(<)" $ tacREWRITE [thmWF_IND, wfNUM_PRIM]

thmWF_LEX :: WFCtxt thry => HOL cls thry HOLThm
thmWF_LEX = cacheProof "thmWF_LEX" ctxtWF .
    prove [str| !R:A->A->bool S:B->B->bool. WF(R) /\ WF(S)
                ==> WF(\(r1,s1) (r2,s2). R r1 r2 \/ (r1 = r2) /\ S s1 s2) |] $
      tacSIMP [thmWF_LEX_DEPENDENT, axETA]

thmWF_MEASURE :: WFCtxt thry => HOL cls thry HOLThm
thmWF_MEASURE = cacheProof "thmWF_MEASURE" ctxtWF .
    prove "!m:A->num. WF(MEASURE m)" $
      _REPEAT tacGEN `_THEN` tacREWRITE [defMEASURE] `_THEN`
      tacMATCH_MP thmWF_MEASURE_GEN `_THEN`
      tacMATCH_ACCEPT wfNUM

thmMEASURE_LE ::  WFCtxt thry => HOL cls thry HOLThm
thmMEASURE_LE = cacheProof "thmMEASURE_LE" ctxtWF .
    prove "(!y. MEASURE m y a ==> MEASURE m y b) <=> m(a) <= m(b)" $
      tacREWRITE [defMEASURE] `_THEN` 
      tacMESON [thmNOT_LE, thmLTE_TRANS, thmLT_REFL]

thmWF_FALSE :: WFCtxt thry => HOL cls thry HOLThm
thmWF_FALSE = cacheProof "thmWF_FALSE" ctxtWF .
    prove [str| WF(\x y:A. F) |] $ tacREWRITE [defWF]
