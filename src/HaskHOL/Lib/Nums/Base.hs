module HaskHOL.Lib.Nums.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)
import HaskHOL.Lib.Pair

import HaskHOL.Lib.Nums.B

defIND_SUC :: NumsBCtxt thry => HOL cls thry HOLThm
defIND_SUC = cacheProof "defIND_SUC" ctxtNumsB $ getDefinition "IND_SUC"

defIND_0 :: NumsBCtxt thry => HOL cls thry HOLThm
defIND_0 = cacheProof "defIND_0" ctxtNumsB $ getDefinition "IND_0"

defZERO :: NumsBCtxt thry => HOL cls thry HOLThm
defZERO = cacheProof "defZERO" ctxtNumsB $ getDefinition "_0"

defSUC :: NumsBCtxt thry => HOL cls thry HOLThm
defSUC = cacheProof "defSUC" ctxtNumsB $ getDefinition "SUC"

defNUMERAL :: NumsBCtxt thry => HOL cls thry HOLThm
defNUMERAL = cacheProof "defNUMERAL" ctxtNumsB $ getDefinition "NUMERAL"

rulesNUM_REP :: NumsBCtxt thry => HOL cls thry HOLThm
rulesNUM_REP = cacheProof "rulesNUM_REP" ctxtNumsB $
    do (th, _, _) <- indDefNUM_REP'
       return th

inductNUM_REP :: NumsBCtxt thry => HOL cls thry HOLThm
inductNUM_REP = cacheProof "inductNUM_REP" ctxtNumsB $
    do (_, th, _) <- indDefNUM_REP'
       return th

casesNUM_REP :: NumsBCtxt thry => HOL cls thry HOLThm
casesNUM_REP = cacheProof "casesNUM_REP" ctxtNumsB $
    do (_, _, th) <- indDefNUM_REP'
       return th

indDefNUM_REP' :: NumsBCtxt thry => HOL cls thry (HOLThm, HOLThm, HOLThm)
indDefNUM_REP' = getInductiveDefinition "NUM_REP"

tyDefMkNum :: NumsBCtxt thry => HOL cls thry HOLThm
tyDefMkNum = cacheProof "tyDefMkNum" ctxtNumsB $
    liftM fst tyDefNum'

tyDefDestNum :: NumsBCtxt thry => HOL cls thry HOLThm
tyDefDestNum = cacheProof "tyDefDestNum" ctxtNumsB $
    liftM snd tyDefNum'

tyDefNum' ::NumsBCtxt thry => HOL cls thry (HOLThm, HOLThm)
tyDefNum' = getBasicTypeDefinition "num"

thmIND_SUC_0_EXISTS :: NumsBCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0_EXISTS = cacheProof "thmIND_SUC_0_EXISTS" ctxtNumsB $
    prove [str| ?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ 
                                 (!x. ~(f x = z)) |] $
      tacX_CHOOSE "f:ind -> ind" axINFINITY `_THEN`
      tacEXISTS "f:ind -> ind" `_THEN`
      _POP_ASSUM tacMP `_THEN`
      tacREWRITE [defONE_ONE, defONTO] `_THEN`
      tacMESON_NIL

thmIND_SUC_SPEC :: NumsBCtxt thry => HOL cls thry HOLThm
thmIND_SUC_SPEC = cacheProof "thmIND_SUC_SPEC" ctxtNumsB $
  do th1 <- ruleGSYM defIND_SUC
     th2 <- ruleREWRITE [th1] =<< ruleSELECT thmIND_SUC_0_EXISTS
     th3 <- ruleGSYM defIND_0
     ruleREWRITE [th3] =<< ruleSELECT th2

thmIND_SUC_INJ :: NumsBCtxt thry => HOL cls thry HOLThm
thmIND_SUC_INJ = cacheProof "thmIND_SUC_INJ" ctxtNumsB $
    liftM fst $ ruleCONJ_PAIR thmIND_SUC_SPEC

thmIND_SUC_0 :: NumsBCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0 = cacheProof "thmIND_SUC_0" ctxtNumsB $
    liftM snd $ ruleCONJ_PAIR thmIND_SUC_SPEC

thmNUM_ZERO_PRIM :: NumsBCtxt thry => HOL cls thry HOLThm
thmNUM_ZERO_PRIM = cacheProof "thmNUM_ZERO_PRIM" ctxtNumsB $
    prove [str| _0 = 0 |] $ tacREWRITE [defNUMERAL]

thmNOT_SUC' :: NumsBCtxt thry => HOL cls thry HOLThm
thmNOT_SUC' = cacheProof "thmNOT_SUC'" ctxtNumsB $
      prove [str| !n. ~(SUC n = _0) |]
        (tacREWRITE [defSUC, defZERO] `_THEN`
         tacMESON [rulesNUM_REP, tyDefMkNum, tyDefDestNum, thmIND_SUC_0])

thmNOT_SUC :: NumsBCtxt thry => HOL cls thry HOLThm
thmNOT_SUC = cacheProof "thmNOT_SUC" ctxtNumsB $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< thmNOT_SUC'

thmSUC_INJ :: NumsBCtxt thry => HOL cls thry HOLThm
thmSUC_INJ = cacheProof "thmSUC_INJ" ctxtNumsB $
    do (mk, dest) <- pairMapM toHTm ("mk_num", "dest_num")
       prove [str| !m n. SUC m = SUC n <=> m = n |] $
         _REPEAT tacGEN `_THEN` tacREWRITE [defSUC] `_THEN`
         tacEQ `_THEN` tacDISCH `_THEN` tacASM_REWRITE_NIL `_THEN`
         _POP_ASSUM (tacMP . ruleAP_TERM dest) `_THEN`
         _SUBGOAL_THEN "!p. NUM_REP (IND_SUC (dest_num p))" tacMP `_THENL`
         [ tacGEN `_THEN` 
           liftM1 tacMATCH_MP (ruleCONJUNCT2 rulesNUM_REP)
         , _ALL
         ] `_THEN`
         tacREWRITE [tyDefMkNum, tyDefDestNum] `_THEN`
         tacDISCH `_THEN` tacASM_REWRITE [thmIND_SUC_INJ] `_THEN`
         _DISCH_THEN (tacMP . ruleAP_TERM mk) `_THEN`
         tacREWRITE [tyDefMkNum]

inductionNUM' :: NumsBCtxt thry => HOL cls thry HOLThm
inductionNUM' = cacheProof "inductionNUM'" ctxtNumsB $
      prove [str| !P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n |]
        (_REPEAT tacSTRIP `_THEN`
         tacMP (ruleSPEC [str| \i. NUM_REP i /\ 
                                   P(mk_num i):bool |] inductNUM_REP) `_THEN`
         tacASM_REWRITE [ruleGSYM defZERO, rulesNUM_REP] `_THEN`
         wComb (\ (Goal _ g) -> flip _SUBGOAL_THEN (\ t -> tacREWRITE [t]) . 
                                  fromJust $ funpowM 2 lHand g) `_THENL`
         [ _REPEAT tacSTRIP `_THENL`
           [ liftM1 tacMATCH_MP (ruleCONJUNCT2 rulesNUM_REP) `_THEN` 
             tacASM_REWRITE_NIL
           , _SUBGOAL_THEN "mk_num (IND_SUC i) = SUC (mk_num i)" 
             tacSUBST1 `_THENL`
             [ tacREWRITE [defSUC] `_THEN` _REPEAT tacAP_TERM `_THEN`
               tacCONV convSYM `_THEN` 
               tacREWRITE [ruleGSYM tyDefDestNum] `_THEN`
               _FIRST_ASSUM tacMATCH_ACCEPT
             , _FIRST_ASSUM tacMATCH_MP `_THEN` _FIRST_ASSUM tacMATCH_ACCEPT
             ]
           ]
         , _DISCH_THEN (tacMP . ruleSPEC "dest_num n") `_THEN`
           tacREWRITE [ tyDefMkNum, tyDefDestNum ]
         ])

inductionNUM :: NumsBCtxt thry => HOL cls thry HOLThm
inductionNUM = cacheProof "inductionNUM" ctxtNumsB $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< inductionNUM'

thmNUM_AXIOM' :: NumsBCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM' = cacheProof "thmNUM_AXIOM'" ctxtNumsB $
      prove [str| ! (e:A) f. ?!fn. (fn _0 = e) /\ 
                             (!n. fn (SUC n) = f (fn n) n) |]
        (_REPEAT tacGEN `_THEN` tacONCE_REWRITE [thmEXISTS_UNIQUE] `_THEN` 
         tacCONJ `_THENL`
         [ (tacMP . proveInductiveRelationsExist) 
             [str| PRG _0 e /\ 
                   (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n)) |] `_THEN`
           _DISCH_THEN (_CHOOSE_THEN (_CONJUNCTS_THEN2 tacASSUME tacMP)) `_THEN`
           _DISCH_THEN (_CONJUNCTS_THEN2 tacASSUME 
                        (tacASSUME . ruleGSYM)) `_THEN`
           _SUBGOAL_THEN [str| !n:num. ?!y:A. PRG n y |] tacMP `_THENL`
           [ tacMATCH_MP inductionNUM' `_THEN` _REPEAT tacSTRIP `_THEN`
             _FIRST_ASSUM (\ th -> tacGEN_REWRITE convBINDER 
                                     [ruleGSYM th]) `_THEN`
             (\ gl -> do th <- ruleGSYM thmNOT_SUC'
                         ths <- sequence [ thmNOT_SUC', thmSUC_INJ
                                         , thmEXISTS_UNIQUE_REFL ]
                         tacREWRITE (th:ths) gl) `_THEN`
             tacREWRITE [thmUNWIND1] `_THEN`
             tacUNDISCH [str| ?!y. PRG (n:num) (y:A) |] `_THEN`
             tacREWRITE [thmEXISTS_UNIQUE] `_THEN`
             _DISCH_THEN (_CONJUNCTS_THEN2 (tacX_CHOOSE "y:A") 
                          tacASSUME) `_THEN`
             _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THENL`
             [ _MAP_EVERY tacEXISTS ["(f:A->num->A) y n", "y:A"]
             , tacAP_THM `_THEN` tacAP_TERM `_THEN` _FIRST_ASSUM tacMATCH_MP
             ] `_THEN`
             tacASM_REWRITE_NIL
           , tacREWRITE [thmUNIQUE_SKOLEM_ALT] `_THEN`
             _DISCH_THEN (_X_CHOOSE_THEN "fn:num->A" 
                          (tacASSUME . ruleGSYM)) `_THEN`
             tacEXISTS "fn:num->A" `_THEN` tacASM_REWRITE_NIL `_THEN`
             tacGEN `_THEN` _FIRST_ASSUM (tacMATCH_MP . 
                                          ruleCONJUNCT2) `_THEN`
             _FIRST_ASSUM (\ th -> tacGEN_REWRITE id [ruleGSYM th]) `_THEN` 
             tacREFL
           ]
         , _REPEAT tacSTRIP `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
           tacMATCH_MP inductionNUM' `_THEN` tacASM_REWRITE_NIL `_THEN`
           _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL
         ])

thmNUM_AXIOM :: NumsBCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM = cacheProof "thmNUM_AXIOM" ctxtNumsB $
    ruleGEN_REWRITE convDEPTH [thmNUM_ZERO_PRIM] =<< thmNUM_AXIOM'

recursionNUM :: NumsBCtxt thry => HOL cls thry HOLThm
recursionNUM = cacheProof "recursionNUM" ctxtNumsB $
    do pth <- thmNUM_AXIOM
       let avs = fst . stripForall $ concl pth
       ruleGENL avs =<< ruleEXISTENCE =<< ruleSPECL avs pth

recursionStdNUM :: NumsBCtxt thry => HOL cls thry HOLThm
recursionStdNUM = cacheProof "recursionStdNUM" ctxtNumsB $
    prove [str| !e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n)) |] $
      _REPEAT tacGEN `_THEN`
      tacMP (ruleISPECL ["e:Z", [str| (\z n. (f:num->Z->Z) n z) |]] 
             recursionNUM) `_THEN`
      tacREWRITE_NIL

defBIT0'' :: PairCtxt thry => HOL Theory thry HOLThm
defBIT0'' = newDefinition "BIT0"
    [str| BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC(fn n))) |]

defBIT1' :: PairCtxt thry => HOL Theory thry HOLThm
defBIT1' = newDefinition "BIT1"
    [str| BIT1 n = SUC (BIT0 n) |]
