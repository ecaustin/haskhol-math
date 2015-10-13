module HaskHOL.Lib.IndTypes.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getSpecification, getDefinition, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF

import HaskHOL.Lib.IndTypes.Pre2

defINJN :: HOL cls thry HOLThm
defINJN = unsafeCacheProof "defINJN" $ getDefinition "INJN"

defINJA :: HOL cls thry HOLThm
defINJA = unsafeCacheProof "defINJA" $ getDefinition "INJA"

defINJF :: HOL cls thry HOLThm
defINJF = unsafeCacheProof "defINJF" $ getDefinition "INJF"

defINJP :: HOL cls thry HOLThm
defINJP = unsafeCacheProof "defINJP" $ getDefinition "INJP"

defZCONSTR :: HOL cls thry HOLThm
defZCONSTR = unsafeCacheProof "defZCONSTR" $ getDefinition "ZCONSTR"

defZBOT :: HOL cls thry HOLThm
defZBOT = unsafeCacheProof "defZBOT" $ getDefinition "ZBOT"

defBOTTOM :: HOL cls thry HOLThm
defBOTTOM = unsafeCacheProof "defBOTTOM" $ getDefinition "BOTTOM"

defCONSTR :: HOL cls thry HOLThm
defCONSTR = unsafeCacheProof "defCONSTR" $ getDefinition "CONSTR"

tyDefMkRecspace :: HOL cls thry HOLThm
tyDefMkRecspace = unsafeCacheProof "tyDefMkRecspace" . liftM fst $
    getBasicTypeDefinition "recspace"

tyDefDestRecspace :: HOL cls thry HOLThm
tyDefDestRecspace = unsafeCacheProof "tyDefDestRecspace" . liftM snd $
    getBasicTypeDefinition "recspace"

specNUMPAIR_DEST :: HOL cls thry HOLThm
specNUMPAIR_DEST = unsafeCacheProof "specNUMPAIR_DEST" $
    getSpecification ["NUMFST", "NUMSND"]

specNUMSUM_DEST :: HOL cls thry HOLThm
specNUMSUM_DEST = unsafeCacheProof "specNUMSUM_DEST" $
    getSpecification ["NUMLEFT", "NUMRIGHT"]

rulesZRECSPACE :: HOL cls thry HOLThm
rulesZRECSPACE = unsafeCacheProof "rulesZRECSPACE" $
    do (th, _, _) <- getInductiveDefinition "ZRECSPACE"
       return th

inductZRECSPACE :: HOL cls thry HOLThm
inductZRECSPACE = unsafeCacheProof "inductZRECSPACE" $
    do (_, th, _) <- getInductiveDefinition "ZRECSPACE"
       return th

thmINJN_INJ ::  BoolCtxt thry => HOL cls thry HOLThm
thmINJN_INJ = unsafeCacheProof "thmINJN_INJ" $
    do tm1 <- toHTm "n1:num"
       tm2 <- toHTm "a:A"
       prove "!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)" $
         _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
         tacASM_REWRITE_NIL `_THEN` 
         _POP_ASSUM (\ th g -> do th' <- ruleREWRITE [defINJN] th
                                  tacMP (ruleAP_THM th' tm1) g) `_THEN`
         _DISCH_THEN (tacMP . flip ruleAP_THM tm2) `_THEN` tacREWRITE [thmBETA]

thmINJA_INJ :: ClassicCtxt thry => HOL cls thry HOLThm
thmINJA_INJ = unsafeCacheProof "thmINJA_INJ" .
    prove "!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)" $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [defINJA, thmFUN_EQ] `_THEN` 
      tacEQ `_THENL`
      [ _DISCH_THEN (tacMP . ruleSPEC "a1:A") `_THEN` tacREWRITE_NIL
      , _DISCH_THEN tacSUBST1 `_THEN` tacREWRITE_NIL
      ]

thmINJF_INJ :: ClassicCtxt thry => HOL cls thry HOLThm
thmINJF_INJ = unsafeCacheProof "thmINJF_INJ" $
    do tm1 <- toHTm "a:A"
       tm2 <- toHTm "NUMPAIR n m"
       prove "!f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2)" $
         _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
         tacASM_REWRITE_NIL `_THEN` tacREWRITE [thmFUN_EQ] `_THEN`
         _MAP_EVERY tacX_GEN ["n:num", "m:num", "a:A"] `_THEN`
         _POP_ASSUM (tacMP . ruleREWRITE [defINJF]) `_THEN`
         _DISCH_THEN (tacMP <#< flip ruleAP_THM tm1 <=< flip ruleAP_THM tm2) `_THEN`
         tacREWRITE [specNUMPAIR_DEST]

thmINJP_INJ :: ClassicCtxt thry => HOL cls thry HOLThm
thmINJP_INJ = unsafeCacheProof "thmINJP_INJ" $
    do tm <- toHTm "NUMSUM b n"
       prove [str| !(f1:num->A->bool) f1' f2 f2'.
                   (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\ (f2 = f2') |] $
         _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
         tacASM_REWRITE_NIL `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
         tacREWRITE [thmAND_FORALL] `_THEN` tacX_GEN "n:num" `_THEN`
         _POP_ASSUM (tacMP . ruleREWRITE [defINJP]) `_THEN`
         _DISCH_THEN (tacMP . ruleGEN "b:bool" . flip ruleAP_THM tm) `_THEN`
         _DISCH_THEN (\ th -> tacMP (ruleSPEC "T" th) `_THEN` 
                              tacMP (ruleSPEC "F" th)) `_THEN`
         tacASM_SIMP [specNUMSUM_DEST, axETA]

thmMK_REC_INJ :: BoolCtxt thry => HOL cls thry HOLThm
thmMK_REC_INJ = unsafeCacheProof "thmMK_REC_INJ" .
    prove [str| !x y. (_mk_rec x :(A)recspace = _mk_rec y) ==> 
                      (ZRECSPACE x /\ ZRECSPACE y ==> (x = y)) |] $
      _REPEAT tacGEN `_THEN` tacDISCH `_THEN`
      tacREWRITE [tyDefDestRecspace] `_THEN`
      _DISCH_THEN (\ th -> tacONCE_REWRITE [ruleGSYM th]) `_THEN`
      tacASM_REWRITE_NIL

thmDEST_REC_INJ :: BoolCtxt thry => HOL cls thry HOLThm
thmDEST_REC_INJ = unsafeCacheProof "thmDEST_REC_INJ" $
    do tm <- toHTm "_mk_rec:(num->A->bool)->(A)recspace"
       prove "!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)" $
         _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
         tacASM_REWRITE_NIL `_THEN` _POP_ASSUM (tacMP . ruleAP_TERM tm) `_THEN`
         tacREWRITE [tyDefMkRecspace]

thmZCONSTR_ZBOT :: NumsCtxt thry => HOL cls thry HOLThm
thmZCONSTR_ZBOT = unsafeCacheProof "thmZCONSTR_ZBOT" .
    prove "!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)" $
      tacREWRITE [ defZCONSTR, defZBOT
                 , thmINJP_INJ, thmINJN_INJ, thmNOT_SUC ]

thmCONSTR_INJ :: NumsCtxt thry => HOL cls thry HOLThm
thmCONSTR_INJ = unsafeCacheProof "thmCONSTR_INJ" .
    prove [str| !c1 i1 r1 c2 i2 r2. 
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

thmCONSTR_IND :: ClassicCtxt thry => HOL cls thry HOLThm
thmCONSTR_IND = unsafeCacheProof "thmCONSTR_INJD" .
    prove [str| !P. P(BOTTOM) /\
                (!c i r. (!n. P(r n)) ==> P(CONSTR c i r)) ==> 
                         !x:(A)recspace. P(x) |] $
      _REPEAT tacSTRIP `_THEN`
      tacMP (ruleSPEC [str| \z:num->A->bool. ZRECSPACE(z) /\ P(_mk_rec z) |]
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
        _DISCH_THEN (tacMP . ruleSPEC "_dest_rec (x:(A)recspace)") `_THEN`
        tacREWRITE [tyDefMkRecspace] `_THEN`
        tacREWRITE [ruleITAUT [str| (a ==> a /\ b) <=> (a ==> b) |]] `_THEN`
        _DISCH_THEN tacMATCH_MP `_THEN`
        tacREWRITE [tyDefMkRecspace, tyDefDestRecspace]
      ]

thmCONSTR_BOT :: NumsCtxt thry => HOL cls thry HOLThm
thmCONSTR_BOT = unsafeCacheProof "thmCONSTR_BOT" .
    prove "!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)" $
      _REPEAT tacGEN `_THEN` 
      tacREWRITE [defCONSTR, defBOTTOM] `_THEN`
      _DISCH_THEN (tacMP . ruleMATCH_MP thmMK_REC_INJ) `_THEN`
      tacREWRITE [thmZCONSTR_ZBOT, rulesZRECSPACE] `_THEN`
      tacMATCH_MP (ruleCONJUNCT2 rulesZRECSPACE) `_THEN`
      tacREWRITE [tyDefMkRecspace, tyDefDestRecspace]

thmCONSTR_REC :: NumsCtxt thry => HOL cls thry HOLThm
thmCONSTR_REC = unsafeCacheProof "thmCONSTR_REC" .
    prove [str| !Fn:num->A->(num->(A)recspace)->(num->B)->B.
                     ?f. (!c i r. f (CONSTR c i r) = 
                         Fn c i r (\n. f (r n))) |] $
         _REPEAT tacSTRIP `_THEN` (tacMP . proveInductiveRelationsExist)
           [str| (Z:(A)recspace->B->bool) BOTTOM b /\
                 (!c i r y. (!n. Z (r n) (y n)) ==> 
                            Z (CONSTR c i r) (Fn c i r y)) |] `_THEN`
         _DISCH_THEN (_CHOOSE_THEN (_CONJUNCTS_THEN2 
                                      tacSTRIP_ASSUME tacMP)) `_THEN`
         _DISCH_THEN (_CONJUNCTS_THEN2 tacASSUME (tacASSUME . ruleGSYM)) `_THEN`
         _SUBGOAL_THEN "!x. ?!y. (Z:(A)recspace->B->bool) x y" tacMP `_THENL`
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
             _DISCH_THEN (_X_CHOOSE_THEN "y:num->B" tacASSUME) `_THEN`
             tacREWRITE [thmEXISTS_UNIQUE] `_THEN`
             _FIRST_ASSUM (\ th -> _CHANGED 
                             (tacONCE_REWRITE [ruleGSYM th])) `_THEN`
             tacCONJ `_THENL`
             [ tacEXISTS 
                 "(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y" `_THEN`
               tacREWRITE [ thmCONSTR_BOT, thmCONSTR_INJ
                          , ruleGSYM thmCONJ_ASSOC ] `_THEN`
               tacREWRITE [thmUNWIND1, thmRIGHT_EXISTS_AND] `_THEN`
               tacEXISTS "y:num->B" `_THEN` tacASM_REWRITE_NIL
             , tacREWRITE [ thmCONSTR_BOT, thmCONSTR_INJ
                          , ruleGSYM thmCONJ_ASSOC ] `_THEN`
               tacREWRITE [thmUNWIND1, thmRIGHT_EXISTS_AND] `_THEN`
               _REPEAT tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
               _REPEAT tacAP_TERM `_THEN` tacONCE_REWRITE [thmFUN_EQ] `_THEN`
               tacX_GEN "w:num" `_THEN` _FIRST_ASSUM tacMATCH_MP `_THEN`
               tacEXISTS "w:num" `_THEN` tacASM_REWRITE_NIL
             ]
           ]
         , tacREWRITE [thmUNIQUE_SKOLEM_ALT] `_THEN`
           _DISCH_THEN (_X_CHOOSE_THEN "fn:(A)recspace->B" 
                          (tacASSUME . ruleGSYM)) `_THEN`
           tacEXISTS "fn:(A)recspace->B" `_THEN` tacASM_REWRITE_NIL `_THEN`
           _REPEAT tacGEN `_THEN` _FIRST_ASSUM tacMATCH_MP `_THEN` 
           tacGEN `_THEN` 
           _FIRST_ASSUM (\ th -> tacGEN_REWRITE id [ruleGSYM th]) `_THEN`
           tacREWRITE [thmBETA]
         ]

thmINJ_INVERSE2 :: WFCtxt thry => HOL cls thry HOLThm
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

thmNUMPAIR_INJ_LEMMA :: WFCtxt thry => HOL cls thry HOLThm
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

thmNUMSUM_INJ :: WFCtxt thry => HOL cls thry HOLThm
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

thmNUMPAIR_INJ :: WFCtxt thry => HOL cls thry HOLThm
thmNUMPAIR_INJ = cacheProof "thmNUMPAIR_INJ" ctxtWF $
    prove [str| !x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> 
                              (x1 = x2) /\ (y1 = y2) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN`
      _FIRST_ASSUM (tacSUBST_ALL . ruleMATCH_MP thmNUMPAIR_INJ_LEMMA) `_THEN`
      _POP_ASSUM tacMP `_THEN` tacREWRITE [defNUMPAIR] `_THEN`
      tacREWRITE [thmEQ_MULT_LCANCEL, thmEQ_ADD_RCANCEL, thmEXP_EQ_0, thmARITH]

--EvNote: need list for distintness and injectivity stores because of dupe keys
data RectypeNet = RectypeNet !(Net GConversion) deriving Typeable

deriveSafeCopy 0 'base ''RectypeNet

getNet :: Query RectypeNet (Net GConversion)
getNet =
    do (RectypeNet net) <- ask
       return net

putNet :: Net GConversion -> Update RectypeNet ()
putNet net = put (RectypeNet net)

makeAcidic ''RectypeNet ['getNet, 'putNet]

data InductiveTypes = 
    InductiveTypes !(Map Text (HOLThm, HOLThm)) deriving Typeable

putInductiveTypes :: Map Text (HOLThm, HOLThm) -> Update InductiveTypes ()
putInductiveTypes m =
    put (InductiveTypes m)

getInductiveTypes :: Query InductiveTypes (Map Text (HOLThm, HOLThm))
getInductiveTypes =
    do (InductiveTypes m) <- ask
       return m

addInductiveType :: Text -> (HOLThm, HOLThm) -> Update InductiveTypes ()
addInductiveType s ths =
    do (InductiveTypes m) <- get
       put (InductiveTypes (mapInsert s ths m))

getInductiveType :: Text -> Query InductiveTypes (Maybe (HOLThm, HOLThm))
getInductiveType s =
    do (InductiveTypes m) <- ask
       return $! mapLookup s m

deriveSafeCopy 0 'base ''InductiveTypes

makeAcidic ''InductiveTypes 
  ['putInductiveTypes, 'getInductiveTypes, 'addInductiveType, 'getInductiveType]

data DistinctnessStore = 
    DistinctnessStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''DistinctnessStore

getDistinctnessStore :: Query DistinctnessStore [(Text, HOLThm)]
getDistinctnessStore = 
    do (DistinctnessStore m) <- ask
       return m

addDistinctnessStore :: Text -> [HOLThm] -> Update DistinctnessStore ()
addDistinctnessStore tyname ths =
    do (DistinctnessStore m) <- get
       put (DistinctnessStore (map (\ x -> (tyname, x)) ths ++ m))

putDistinctnessStore :: [(Text, HOLThm)] -> Update DistinctnessStore ()
putDistinctnessStore m =
    put (DistinctnessStore m)

makeAcidic ''DistinctnessStore 
    ['getDistinctnessStore, 'addDistinctnessStore, 'putDistinctnessStore]

data InjectivityStore = InjectivityStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''InjectivityStore

getInjectivityStore :: Query InjectivityStore [(Text, HOLThm)]
getInjectivityStore =
    do (InjectivityStore m) <- ask
       return m

addInjectivityStore :: Text -> [HOLThm] -> Update InjectivityStore ()
addInjectivityStore tyname ths =
    do (InjectivityStore m) <- get
       put (InjectivityStore (map (\ x -> (tyname, x)) ths ++ m))

makeAcidic ''InjectivityStore ['getInjectivityStore, 'addInjectivityStore]


rehashRectypeNet :: BoolCtxt thry => HOL Theory thry ()
rehashRectypeNet =
    do acid1 <- openLocalStateHOL (DistinctnessStore [])
       ths1 <- liftM (map snd) $ queryHOL acid1 GetDistinctnessStore
       closeAcidStateHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       ths2 <- liftM (map snd) $ queryHOL acid2 GetInjectivityStore
       closeAcidStateHOL acid2
       canonThl <- foldrM (mkRewrites False) [] $ ths1 ++ ths2
       net' <- liftO $ foldrM (netOfThm True) netEmpty canonThl
       acid3 <- openLocalStateHOL (RectypeNet netEmpty)
       updateHOL acid3 (PutNet net')
       createCheckpointAndCloseHOL acid3

extendRectypeNet :: WFCtxt thry => (Text, (Int, HOLThm, HOLThm)) 
                 -> HOL Theory thry ()
extendRectypeNet (tyname, (_, _, rth)) =
    do ths1 <- liftM (:[]) (proveConstructorsDistinct rth) <|> return []
       ths2 <- liftM (:[]) (proveConstructorsInjective rth) <|> return []
       acid1 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid1 (AddDistinctnessStore tyname ths1)
       createCheckpointAndCloseHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       updateHOL acid2 (AddInjectivityStore tyname ths2)
       createCheckpointAndCloseHOL acid2
       rehashRectypeNet

basicRectypeNet :: BoolCtxt thry => HOL cls thry (Net GConversion)
basicRectypeNet =
    do acid <- openLocalStateHOL (RectypeNet netEmpty)
       net <- queryHOL acid GetNet
       closeAcidStateHOL acid
       return net
