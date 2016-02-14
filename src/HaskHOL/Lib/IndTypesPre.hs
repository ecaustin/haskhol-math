{-|
  Module:    HaskHOL.Lib.IndTypesPre
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.IndTypesPre
    ( IndTypesPreCtxt
    , ctxtIndTypesPre
    , indTypesPre
    , thmNUMPAIR_INJ_LEMMA
    , thmNUMSUM_INJ
    , thmNUMPAIR_INJ
    , thmINJ_INVERSE2
    , defINJA
    , defINJF
    , defINJN
    , defINJP
    , defZCONSTR
    , defZBOT
    , defBOTTOM
    , defCONSTR
    , defFNIL
    , defFCONS
    , specNUMPAIR_DEST
    , specNUMSUM_DEST
    , tyDefMkRecspace
    , tyDefDestRecspace
    , rulesZRECSPACE
    , inductZRECSPACE
    , casesZRECSPACE
    , thmINJN_INJ
    , thmINJP_INJ
    , thmINJA_INJ
    , thmINJF_INJ
    , thmDEST_REC_INJ
    , thmMK_REC_INJ
    , thmZCONSTR_ZBOT
    , thmCONSTR_INJ
    , thmCONSTR_IND
    , thmCONSTR_BOT
    , thmCONSTR_REC
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification)

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypesPre.Base
import HaskHOL.Lib.IndTypesPre.Context
import HaskHOL.Lib.IndTypesPre.PQ

defINJA :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defINJA = cacheProof "defINJA" ctxtIndTypesPre $ getDefinition "INJA"

defINJF :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defINJF = cacheProof "defINJF" ctxtIndTypesPre $ getDefinition "INJF"

defINJN :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defINJN = cacheProof "defINJN" ctxtIndTypesPre $ getDefinition "INJN"

defINJP :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defINJP = cacheProof "defINJP" ctxtIndTypesPre $ getDefinition "INJP"

defZCONSTR :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defZCONSTR = cacheProof "defZCONSTR" ctxtIndTypesPre $ getDefinition "ZCONSTR"

defZBOT :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defZBOT = cacheProof "defZBOT" ctxtIndTypesPre $ getDefinition "ZBOT"

defBOTTOM :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defBOTTOM = cacheProof "defBOTTOM" ctxtIndTypesPre $ getDefinition "BOTTOM"

defCONSTR :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defCONSTR = cacheProof "defCONSTR" ctxtIndTypesPre $ getDefinition "CONSTR"

defFNIL :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defFNIL = cacheProof "defFNIL" ctxtIndTypesPre $ getDefinition "FNIL"

defFCONS :: IndTypesPreCtxt thry => HOL cls thry HOLThm
defFCONS = cacheProof "defFCONS" ctxtIndTypesPre $ 
    getRecursiveDefinition "FCONS"

specNUMPAIR_DEST :: IndTypesPreCtxt thry => HOL cls thry HOLThm
specNUMPAIR_DEST = cacheProof "specNUMPAIR_DEST" ctxtIndTypesPre $
    getSpecification ["NUMFST", "NUMSND"]

specNUMSUM_DEST :: IndTypesPreCtxt thry => HOL cls thry HOLThm
specNUMSUM_DEST = cacheProof "specNUMSUM_DEST" ctxtIndTypesPre $
    getSpecification ["NUMLEFT", "NUMRIGHT"]

tyDefMkRecspace :: IndTypesPreCtxt thry => HOL cls thry HOLThm
tyDefMkRecspace = cacheProof "tyDefMkRecspace" ctxtIndTypesPre . liftM fst $
    getBasicTypeDefinition "recspace"

tyDefDestRecspace :: IndTypesPreCtxt thry => HOL cls thry HOLThm
tyDefDestRecspace = cacheProof "tyDefDestRecspace" ctxtIndTypesPre . liftM snd $
    getBasicTypeDefinition "recspace"

rulesZRECSPACE :: IndTypesPreCtxt thry => HOL cls thry HOLThm
rulesZRECSPACE = cacheProof "rulesZRECSPACE" ctxtIndTypesPre $
    do (th, _, _) <- getInductiveDefinition "ZRECSPACE"
       return th

inductZRECSPACE :: IndTypesPreCtxt thry => HOL cls thry HOLThm
inductZRECSPACE = cacheProof "inductZRECSPACE" ctxtIndTypesPre $
    do (_, th, _) <- getInductiveDefinition "ZRECSPACE"
       return th

casesZRECSPACE :: IndTypesPreCtxt thry => HOL cls thry HOLThm
casesZRECSPACE = cacheProof "casesZRECSPACE" ctxtIndTypesPre $
    do (_, _, th) <- getInductiveDefinition "ZRECSPACE"
       return th

thmINJN_INJ ::  IndTypesPreCtxt thry => HOL cls thry HOLThm
thmINJN_INJ = cacheProof "thmINJN_INJ" ctxtIndTypesPre $
    prove [txt| !n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN` 
      _POP_ASSUM (\ th -> tacMP (ruleAP_THM (ruleREWRITE [defINJN] th) 
                                   [txt| n1:num |])) `_THEN`
      _DISCH_THEN (tacMP . flip ruleAP_THM [txt| a:A |]) `_THEN` 
      tacREWRITE [thmBETA]

thmINJP_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmINJP_INJ = cacheProof "thmINJP_INJ" ctxtIndTypesPre $
    prove [txt| !(f1:num->A->bool) f1' f2 f2'.
                 (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\ (f2 = f2') |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
      tacREWRITE [thmAND_FORALL] `_THEN` tacX_GEN [txt| n:num |] `_THEN`
      _POP_ASSUM (tacMP . ruleREWRITE [defINJP]) `_THEN`
      _DISCH_THEN (tacMP . ruleGEN [txt| b:bool |] . 
                   flip ruleAP_THM [txt| NUMSUM b n |]) `_THEN`
      _DISCH_THEN (\ th -> tacMP (ruleSPEC [txt| T |] th) `_THEN` 
                           tacMP (ruleSPEC [txt| F |] th)) `_THEN`
      tacASM_SIMP [specNUMSUM_DEST, axETA]

thmINJA_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmINJA_INJ = cacheProof "thmINJA_INJ" ctxtIndTypesPre .
    prove [txt| !a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2) |] $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [defINJA, thmFUN_EQ] `_THEN` 
      tacEQ `_THENL`
      [ _DISCH_THEN (tacMP . ruleSPEC [txt| a1:A |]) `_THEN` tacREWRITE_NIL
      , _DISCH_THEN tacSUBST1 `_THEN` tacREWRITE_NIL
      ]

thmINJF_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmINJF_INJ = cacheProof "thmINJF_INJ" ctxtIndTypesPre $
    prove [txt| !f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN` tacREWRITE [thmFUN_EQ] `_THEN`
      _MAP_EVERY tacX_GEN [[txt| n:num |], [txt| m:num |], [txt| a:A |]] `_THEN`
      _POP_ASSUM (tacMP . ruleREWRITE [defINJF]) `_THEN`
      _DISCH_THEN (tacMP . flip ruleAP_THM [txt| a:A |] . 
                   flip ruleAP_THM [txt| NUMPAIR n m |]) `_THEN`
      tacREWRITE [specNUMPAIR_DEST]

thmDEST_REC_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmDEST_REC_INJ = cacheProof "thmDEST_REC_INJ" ctxtIndTypesPre $
    prove [txt| !x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN` 
      _POP_ASSUM (tacMP . ruleAP_TERM 
                           [txt| _mk_rec:(num->A->bool)->(A)recspace |]) `_THEN`
      tacREWRITE [tyDefMkRecspace]

thmMK_REC_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmMK_REC_INJ = cacheProof "thmMK_REC_INJ" ctxtIndTypesPre .
    prove [txt| !x y. (_mk_rec x :(A)recspace = _mk_rec y) ==> 
                      (ZRECSPACE x /\ ZRECSPACE y ==> (x = y)) |] $
      _REPEAT tacGEN `_THEN` tacDISCH `_THEN`
      tacREWRITE [tyDefDestRecspace] `_THEN`
      _DISCH_THEN (\ th -> tacONCE_REWRITE [ruleGSYM th]) `_THEN`
      tacASM_REWRITE_NIL

thmZCONSTR_ZBOT :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmZCONSTR_ZBOT = cacheProof "thmZCONSTR_ZBOT" ctxtIndTypesPre .
    prove [txt| !c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT) |] $
      tacREWRITE [ defZCONSTR, defZBOT
                 , thmINJP_INJ, thmINJN_INJ, thmNOT_SUC ]

thmCONSTR_INJ :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmCONSTR_INJ = cacheProof "thmCONSTR_INJ" ctxtIndTypesPre .
    prove [txt| !c1 i1 r1 c2 i2 r2. 
                (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>
                (c1 = c2) /\ (i1 = i2) /\ (r1 = r2) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN` 
      _POP_ASSUM (tacMP . ruleREWRITE [defCONSTR]) `_THEN`
      _DISCH_THEN (tacMP . ruleMATCH_MP thmMK_REC_INJ) `_THEN`
      (\ g@(Goal _ w) -> 
           _SUBGOAL_THEN (funpowM 2 lHand w) tacASSUME g) `_THENL`
      [ tacCONJ `_THEN` tacMATCH_MP (ruleCONJUNCT2 rulesZRECSPACE) `_THEN`
        tacREWRITE [tyDefMkRecspace, tyDefDestRecspace]
      , tacASM_REWRITE_NIL `_THEN` tacREWRITE [defZCONSTR] `_THEN`
        tacREWRITE [thmINJP_INJ, thmINJN_INJ, thmINJF_INJ, thmINJA_INJ] `_THEN`
        tacONCE_REWRITE [thmFUN_EQ] `_THEN` tacBETA `_THEN`
        tacREWRITE [thmSUC_INJ, thmDEST_REC_INJ]
      ]

thmCONSTR_IND :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmCONSTR_IND = cacheProof "thmCONSTR_INJD" ctxtIndTypesPre .
    prove [txt| !P. P(BOTTOM) /\
                (!c i r. (!n. P(r n)) ==> P(CONSTR c i r)) ==> 
                         !x:(A)recspace. P(x) |] $
      _REPEAT tacSTRIP `_THEN`
      tacMP (ruleSPEC [txt| \z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z) |]
             inductZRECSPACE) `_THEN`
      tacBETA `_THEN` 
      tacASM_REWRITE [rulesZRECSPACE, ruleGSYM defBOTTOM] `_THEN`
      (\ g@(Goal _ w) -> 
           _SUBGOAL_THEN (funpowM 2 lHand w) tacASSUME g) `_THENL`
      [ _REPEAT tacGEN `_THEN` tacREWRITE [thmFORALL_AND] `_THEN`
        _REPEAT tacSTRIP `_THENL`
        [ tacMATCH_MP (ruleCONJUNCT2 rulesZRECSPACE) `_THEN` tacASM_REWRITE_NIL
        , _FIRST_ASSUM (_ANTE_RES_THEN tacMP) `_THEN`
          tacREWRITE [defCONSTR] `_THEN`
          tacRULE_ASSUM (ruleREWRITE [tyDefDestRecspace]) `_THEN`
          tacASM_SIMP [axETA]
        ]
      , tacASM_REWRITE_NIL `_THEN`
        _DISCH_THEN (tacMP . ruleSPEC [txt|_dest_rec (x:(A)recspace)|]) `_THEN`
        tacREWRITE [tyDefMkRecspace] `_THEN`
        tacREWRITE [ruleITAUT [txt| (a ==> a /\ b) <=> (a ==> b) |]] `_THEN`
        _DISCH_THEN tacMATCH_MP `_THEN`
        tacREWRITE [tyDefMkRecspace, tyDefDestRecspace]
      ]

thmCONSTR_BOT :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmCONSTR_BOT = cacheProof "thmCONSTR_BOT" ctxtIndTypesPre .
    prove [txt| !c i r. ~(CONSTR c i r :(A)recspace = BOTTOM) |] $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [defCONSTR, defBOTTOM] `_THEN`
      _DISCH_THEN (tacMP . ruleMATCH_MP thmMK_REC_INJ) `_THEN`
      tacREWRITE [thmZCONSTR_ZBOT, rulesZRECSPACE] `_THEN`
      tacMATCH_MP (ruleCONJUNCT2 rulesZRECSPACE) `_THEN`
      tacREWRITE [tyDefMkRecspace, tyDefDestRecspace]

thmCONSTR_REC :: IndTypesPreCtxt thry => HOL cls thry HOLThm
thmCONSTR_REC = cacheProof "thmCONSTR_REC" ctxtIndTypesPre .
    prove [txt| !Fn:num->A->(num->(A)recspace)->(num->B)->B.
                     ?f. (!c i r. f (CONSTR c i r) = 
                         Fn c i r (\n. f (r n))) |] $
         _REPEAT tacSTRIP `_THEN` (tacMP . proveInductiveRelationsExist)
           [txt| (Z:(A)recspace->B->bool) BOTTOM b /\
                 (!c i r y. (!n. Z (r n) (y n)) ==> 
                            Z (CONSTR c i r) (Fn c i r y)) |] `_THEN`
         _DISCH_THEN (_CHOOSE_THEN (_CONJUNCTS_THEN2 
                                      tacSTRIP_ASSUME tacMP)) `_THEN`
         _DISCH_THEN (_CONJUNCTS_THEN2 tacASSUME (tacASSUME . ruleGSYM)) `_THEN`
         _SUBGOAL_THEN [txt| !x. ?!y. 
                             (Z:(A)recspace->B->bool) x y |] tacMP `_THENL`
         [ (\ g@(Goal _ w) -> 
                tacMP (rulePART_MATCH rand thmCONSTR_IND w) g) `_THEN` 
           _DISCH_THEN tacMATCH_MP `_THEN` tacCONJ `_THEN` 
           _REPEAT tacGEN `_THENL`
           [ _FIRST_ASSUM (\ t -> tacGEN_REWRITE convBINDER [ruleGSYM t])`_THEN`
             tacREWRITE [ruleGSYM thmCONSTR_BOT, thmEXISTS_UNIQUE_REFL]
           , _DISCH_THEN (tacMP . 
                          ruleREWRITE [thmEXISTS_UNIQUE, thmFORALL_AND]) `_THEN`
             _DISCH_THEN (_CONJUNCTS_THEN2 tacMP tacASSUME) `_THEN`
             _DISCH_THEN (tacMP . ruleREWRITE [thmSKOLEM]) `_THEN`
             _DISCH_THEN (_X_CHOOSE_THEN [txt| y:num->B |] tacASSUME) `_THEN`
             tacREWRITE [thmEXISTS_UNIQUE] `_THEN`
             _FIRST_ASSUM (\ th -> _CHANGED 
                             (tacONCE_REWRITE [ruleGSYM th])) `_THEN`
             tacCONJ `_THENL`
             [ tacEXISTS [txt| (Fn:num->A->(num->(A)recspace)->(num->B)->B) 
                               c i r y |] `_THEN`
               tacREWRITE [ thmCONSTR_BOT, thmCONSTR_INJ
                          , ruleGSYM thmCONJ_ASSOC ] `_THEN`
               tacREWRITE [thmUNWIND1, thmRIGHT_EXISTS_AND] `_THEN`
               tacEXISTS [txt| y:num->B |] `_THEN` tacASM_REWRITE_NIL
             , tacREWRITE [ thmCONSTR_BOT, thmCONSTR_INJ
                          , ruleGSYM thmCONJ_ASSOC ] `_THEN`
               tacREWRITE [thmUNWIND1, thmRIGHT_EXISTS_AND] `_THEN`
               _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
               _REPEAT tacAP_TERM `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
               tacX_GEN [txt| w:num |] `_THEN` _FIRST_ASSUM tacMATCH_MP `_THEN`
               tacEXISTS [txt| w:num |] `_THEN` tacASM_REWRITE_NIL
             ]
           ]
         , tacREWRITE [thmUNIQUE_SKOLEM_ALT] `_THEN`
           _DISCH_THEN (_X_CHOOSE_THEN [txt| fn:(A)recspace->B |] 
                          (tacASSUME . ruleGSYM)) `_THEN`
           tacEXISTS [txt| fn:(A)recspace->B |] `_THEN` 
           tacASM_REWRITE_NIL `_THEN`
           _REPEAT tacGEN `_THEN` _FIRST_ASSUM tacMATCH_MP `_THEN` 
           tacGEN `_THEN` 
           _FIRST_ASSUM (\ th -> tacGEN_REWRITE id [ruleGSYM th]) `_THEN`
           tacREWRITE [thmBETA]
         ]
