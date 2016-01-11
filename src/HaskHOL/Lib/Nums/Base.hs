module HaskHOL.Lib.Nums.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)
import HaskHOL.Lib.Pair

axINFINITY :: HOL cls thry HOLThm
axINFINITY = unsafeCacheProof "axINFINITY" $ getAxiom "axINFINITY"

defONE_ONE :: HOL cls thry HOLThm
defONE_ONE = unsafeCacheProof "defONE_ONE" $ getDefinition "ONE_ONE"

defONTO :: HOL cls thry HOLThm
defONTO = unsafeCacheProof "defONTO" $ getDefinition "ONTO"

defIND_SUC :: HOL cls thry HOLThm
defIND_SUC = unsafeCacheProof "defIND_SUC" $ getDefinition "IND_SUC"

defIND_0 :: HOL cls thry HOLThm
defIND_0 = unsafeCacheProof "defIND_0" $ getDefinition "IND_0"

defZERO :: HOL cls thry HOLThm
defZERO = unsafeCacheProof "defZERO" $ getDefinition "_0"

defSUC :: HOL cls thry HOLThm
defSUC = unsafeCacheProof "defSUC" $ getDefinition "SUC"

defNUMERAL :: HOL cls thry HOLThm
defNUMERAL = unsafeCacheProof "defNUMERAL" $ getDefinition "NUMERAL"

rulesNUM_REP :: HOL cls thry HOLThm
rulesNUM_REP = unsafeCacheProof "rulesNUM_REP" $
    do (th, _, _) <- getInductiveDefinition "NUM_REP"
       return th

inductNUM_REP :: HOL cls thry HOLThm
inductNUM_REP = unsafeCacheProof "inductNUM_REP" $
    do (_, th, _) <- getInductiveDefinition "NUM_REP"
       return th

tyDefMkNum :: HOL cls thry HOLThm
tyDefMkNum = unsafeCacheProof "tyDefMkNum" . 
    liftM fst $ getBasicTypeDefinition "num"

tyDefDestNum :: HOL cls thry HOLThm
tyDefDestNum = unsafeCacheProof "tyDefDestNum" .
    liftM snd $ getBasicTypeDefinition "num"

thmIND_SUC_0_EXISTS :: TriviaCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0_EXISTS = unsafeCacheProof "thmIND_SUC_0_EXISTS" $
    prove [txt| ?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ 
                                 (!x. ~(f x = z)) |] $
      tacX_CHOOSE [txt| f:ind -> ind |] axINFINITY `_THEN`
      tacEXISTS [txt| f:ind -> ind |] `_THEN`
      _POP_ASSUM tacMP `_THEN`
      tacREWRITE [defONE_ONE, defONTO] `_THEN`
      tacMESON_NIL

thmIND_SUC_SPEC :: TriviaCtxt thry => HOL cls thry HOLThm
thmIND_SUC_SPEC = unsafeCacheProof "thmIND_SUC_SPEC" $
  do th1 <- ruleGSYM defIND_SUC
     th2 <- ruleREWRITE [th1] $ ruleSELECT thmIND_SUC_0_EXISTS
     th3 <- ruleGSYM defIND_0
     ruleREWRITE [th3] $ ruleSELECT th2

thmIND_SUC_INJ :: TriviaCtxt thry => HOL cls thry HOLThm
thmIND_SUC_INJ = unsafeCacheProof "thmIND_SUC_INJ" .
    liftM fst $ ruleCONJ_PAIR thmIND_SUC_SPEC

thmIND_SUC_0 :: TriviaCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0 = unsafeCacheProof "thmIND_SUC_0" .
    liftM snd $ ruleCONJ_PAIR thmIND_SUC_SPEC

thmNUM_ZERO_PRIM :: BoolCtxt thry => HOL cls thry HOLThm
thmNUM_ZERO_PRIM = unsafeCacheProof "thmNUM_ZERO_PRIM" .
    prove [txt| _0 = 0 |] $ tacREWRITE [defNUMERAL]

thmNOT_SUC_PRIM :: TriviaCtxt thry => HOL cls thry HOLThm
thmNOT_SUC_PRIM = unsafeCacheProof "thmNOT_SUC_PRIM" .
      prove [txt| !n. ~(SUC n = _0) |] $
        tacREWRITE [defSUC, defZERO] `_THEN`
        tacMESON [rulesNUM_REP, tyDefMkNum, tyDefDestNum, thmIND_SUC_0]

thmNOT_SUC :: TriviaCtxt thry => HOL cls thry HOLThm
thmNOT_SUC = unsafeCacheProof "thmNOT_SUC" $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< thmNOT_SUC_PRIM

thmSUC_INJ :: TriviaCtxt thry => HOL cls thry HOLThm
thmSUC_INJ = unsafeCacheProof "thmSUC_INJ" .
    prove [txt| !m n. SUC m = SUC n <=> m = n |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [defSUC] `_THEN`
      tacEQ `_THEN` tacDISCH `_THEN` tacASM_REWRITE_NIL `_THEN`
      _POP_ASSUM (tacMP . ruleAP_TERM [txt| dest_num |]) `_THEN`
      _SUBGOAL_THEN [txt| !p. NUM_REP (IND_SUC (dest_num p)) |] tacMP `_THENL`
      [ tacGEN `_THEN` 
        tacMATCH_MP (ruleCONJUNCT2 rulesNUM_REP)
      , _ALL
      ] `_THEN`
      tacREWRITE [tyDefMkNum, tyDefDestNum] `_THEN`
      tacDISCH `_THEN` tacASM_REWRITE [thmIND_SUC_INJ] `_THEN`
      _DISCH_THEN (tacMP . ruleAP_TERM [txt| mk_num |]) `_THEN`
      tacREWRITE [tyDefMkNum]

inductionNUM_PRIM :: BoolCtxt thry => HOL cls thry HOLThm
inductionNUM_PRIM = unsafeCacheProof "inductionNUM_PRIM" $
      prove [txt| !P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n |]
        (_REPEAT tacSTRIP `_THEN`
         tacMP (ruleSPEC [txt| \i. NUM_REP i /\ 
                                   P(mk_num i):bool |] inductNUM_REP) `_THEN`
         tacASM_REWRITE [ruleGSYM defZERO, rulesNUM_REP] `_THEN`
         wComb (\ (Goal _ g) -> _SUBGOAL_THEN (try' $ funpowM 2 lHand g) 
                                  (\ t -> tacREWRITE [t])) `_THENL`
         [ _REPEAT tacSTRIP `_THENL`
           [ tacMATCH_MP (ruleCONJUNCT2 rulesNUM_REP) `_THEN` 
             tacASM_REWRITE_NIL
           , _SUBGOAL_THEN [txt| mk_num (IND_SUC i) = SUC (mk_num i) |]
             tacSUBST1 `_THENL`
             [ tacREWRITE [defSUC] `_THEN` 
               _REPEAT tacAP_TERM `_THEN`
               tacCONV convSYM `_THEN` 
               tacREWRITE [ruleGSYM tyDefDestNum] `_THEN`
               _FIRST_ASSUM tacMATCH_ACCEPT
             , _FIRST_ASSUM tacMATCH_MP `_THEN` _FIRST_ASSUM tacMATCH_ACCEPT
             ]
           ]
         , _DISCH_THEN (tacMP . ruleSPEC [txt| dest_num n |]) `_THEN`
           tacREWRITE [ tyDefMkNum, tyDefDestNum ]
         ])

inductionNUM :: BoolCtxt thry => HOL cls thry HOLThm
inductionNUM = unsafeCacheProof "inductionNUM" $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< inductionNUM_PRIM

thmNUM_AXIOM_PRIM :: TriviaCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM_PRIM = unsafeCacheProof "thmNUM_AXIOM_PRIM" $
      prove [txt| ! (e:A) f. ?!fn. (fn _0 = e) /\ 
                             (!n. fn (SUC n) = f (fn n) n) |]
        (_REPEAT tacGEN `_THEN` tacONCE_REWRITE [thmEXISTS_UNIQUE] `_THEN` 
         tacCONJ `_THENL`
         [ (tacMP . proveInductiveRelationsExist) 
             [txt| PRG _0 e /\ 
                   (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n)) |] `_THEN`
           _DISCH_THEN (_CHOOSE_THEN (_CONJUNCTS_THEN2 tacASSUME tacMP)) `_THEN`
           _DISCH_THEN (_CONJUNCTS_THEN2 tacASSUME 
                        (tacASSUME . ruleGSYM)) `_THEN`
           _SUBGOAL_THEN [txt| !n:num. ?!y:A. PRG n y |] tacMP `_THENL`
           [ tacMATCH_MP inductionNUM_PRIM `_THEN` _REPEAT tacSTRIP `_THEN`
             _FIRST_ASSUM (\ th -> tacGEN_REWRITE convBINDER 
                                     [ruleGSYM th]) `_THEN`
             (\ gl -> do th <- ruleGSYM thmNOT_SUC_PRIM
                         ths <- sequence [ thmNOT_SUC_PRIM, thmSUC_INJ
                                         , thmEXISTS_UNIQUE_REFL ]
                         tacREWRITE (th:ths) gl) `_THEN`
             tacREWRITE [thmUNWIND1] `_THEN`
             tacUNDISCH [txt| ?!y. PRG (n:num) (y:A) |] `_THEN`
             tacREWRITE [thmEXISTS_UNIQUE] `_THEN`
             _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE [txt| y:A |]) 
                          tacASSUME) `_THEN`
             _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THENL`
             [ _MAP_EVERY tacEXISTS [[txt| (f:A->num->A) y n |], [txt| y:A |]]
             , tacAP_THM `_THEN` tacAP_TERM `_THEN` _FIRST_ASSUM tacMATCH_MP
             ] `_THEN`
             tacASM_REWRITE_NIL
           , tacREWRITE [thmUNIQUE_SKOLEM_ALT] `_THEN`
             _DISCH_THEN (_X_CHOOSE_THEN [txt| fn:num->A |] 
                          (tacASSUME . ruleGSYM)) `_THEN`
             tacEXISTS [txt| fn:num->A |] `_THEN` tacASM_REWRITE_NIL `_THEN`
             tacGEN `_THEN` _FIRST_ASSUM (tacMATCH_MP . 
                                          ruleCONJUNCT2) `_THEN`
             _FIRST_ASSUM (\ th -> tacGEN_REWRITE id [ruleGSYM th]) `_THEN` 
             tacREFL
           ]
         , _REPEAT tacSTRIP `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
           tacMATCH_MP inductionNUM_PRIM `_THEN` tacASM_REWRITE_NIL `_THEN`
           _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL
         ])

thmNUM_AXIOM :: TriviaCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM = unsafeCacheProof "thmNUM_AXIOM" $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< thmNUM_AXIOM_PRIM

recursionNUM :: TriviaCtxt thry => HOL cls thry HOLThm
recursionNUM = unsafeCacheProof "recursionNUM" $
    do pth <- thmNUM_AXIOM
       let avs = fst . stripForall $ concl pth
       ruleGENL avs =<< ruleEXISTENCE =<< ruleSPECL avs pth

recursionStdNUM :: TriviaCtxt thry => HOL cls thry HOLThm
recursionStdNUM = unsafeCacheProof "recursionStdNUM" $
    prove [txt| !e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n)) |] $
      _REPEAT tacGEN `_THEN`
      tacMP (ruleISPECL ["e:Z", [txt| (\z n. (f:num->Z->Z) n z) |]] 
             recursionNUM) `_THEN`
      tacREWRITE_NIL
    
