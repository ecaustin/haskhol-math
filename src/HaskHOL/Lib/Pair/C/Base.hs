{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, 
             PatternSynonyms, QuasiQuotes, TemplateHaskell, TypeFamilies #-}
module HaskHOL.Lib.Pair.C.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)
import qualified HaskHOL.Deductive as D

import HaskHOL.Lib.Pair.B

tyDefProd :: PairBCtxt thry => HOL cls thry HOLThm
tyDefProd = cacheProof "tyDefProd" ctxtPairB $ getTypeDefinition "prod"

defCOMMA :: PairBCtxt thry => HOL cls thry HOLThm
defCOMMA = cacheProof "defCOMMA" ctxtPairB $ D.getDefinition ","

defFST :: PairBCtxt thry => HOL cls thry HOLThm
defFST = cacheProof "defFST" ctxtPairB $ D.getDefinition "FST"

defSND :: PairBCtxt thry => HOL cls thry HOLThm
defSND = cacheProof "defSND" ctxtPairB $ D.getDefinition "SND"

thmREP_ABS_PAIR :: PairBCtxt thry => HOL cls thry HOLThm
thmREP_ABS_PAIR = cacheProof "thmREP_ABS_PAIR" ctxtPairB $
    prove "!(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y" $
      tacMESON [tyDefProd]

thmPAIR_SURJECTIVE :: PairBCtxt thry => HOL cls thry HOLThm
thmPAIR_SURJECTIVE = cacheProof "thmPAIR_SURJECTIVE" ctxtPairB $
    do tm <- toHTm "ABS_prod:(A->B->bool)->A#B"
       (th1, th2) <- ruleCONJ_PAIR tyDefProd
       prove "!p:A#B. ?x y. p = x,y" $
         tacGEN `_THEN` tacREWRITE [defCOMMA] `_THEN`
         tacMP (ruleSPEC "REP_prod p :A->B->bool" th2) `_THEN` 
         tacREWRITE [th1] `_THEN`
         _DISCH_THEN (_X_CHOOSE_THEN "a:A" 
                      (_X_CHOOSE_THEN "b:B" tacMP)) `_THEN`
         _DISCH_THEN (tacMP . ruleAP_TERM tm) `_THEN`
         tacREWRITE [th1] `_THEN` _DISCH_THEN tacSUBST1 `_THEN`
         _MAP_EVERY tacEXISTS ["a:A", "b:B"] `_THEN` tacREFL

thmPAIR_EQ :: PairBCtxt thry => HOL cls thry HOLThm
thmPAIR_EQ = cacheProof "thmPAIR_EQ" ctxtPairB $
    do tm <- toHTm "REP_prod:A#B->A->B->bool"
       prove [str| !(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b) |] $
         _REPEAT tacGEN `_THEN` tacEQ `_THENL`
         [ tacREWRITE [defCOMMA] `_THEN`
           _DISCH_THEN (tacMP . ruleAP_TERM tm) `_THEN`
           tacREWRITE [thmREP_ABS_PAIR] `_THEN` 
           tacREWRITE [defMK_PAIR, thmFUN_EQ]
         , _ALL
         ] `_THEN`
         tacMESON_NIL

thmFST :: PairBCtxt thry => HOL cls thry HOLThm
thmFST = cacheProof "thmFST" ctxtPairB $
    prove "!(x:A) (y:B). FST(x,y) = x" $
      _REPEAT tacGEN `_THEN` tacREWRITE[defFST] `_THEN`
      tacMATCH_MP thmSELECT_UNIQUE `_THEN` tacGEN `_THEN` tacBETA `_THEN`
      tacREWRITE [thmPAIR_EQ] `_THEN` tacEQ `_THEN`
      tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
      tacEXISTS "y:B" `_THEN` tacASM_REWRITE_NIL

thmSND :: PairBCtxt thry => HOL cls thry HOLThm
thmSND = cacheProof "thmSND" ctxtPairB $
    prove "!(x:A) (y:B). SND(x,y) = y" $
      _REPEAT tacGEN `_THEN` tacREWRITE [defSND] `_THEN`
      tacMATCH_MP thmSELECT_UNIQUE `_THEN` tacGEN `_THEN` tacBETA `_THEN`
      tacREWRITE [thmPAIR_EQ] `_THEN` tacEQ `_THEN`
      tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
      tacEXISTS "x:A" `_THEN` tacASM_REWRITE_NIL

thmPAIR :: PairBCtxt thry => HOL cls thry HOLThm
thmPAIR = cacheProof "thmPAIR" ctxtPairB $
    prove "!x:A#B. FST x,SND x = x" $
      tacGEN `_THEN` 
      _X_CHOOSE_THEN "a:A" (_X_CHOOSE_THEN "b:B" tacSUBST1)
        (ruleSPEC "x:A#B" thmPAIR_SURJECTIVE) `_THEN`
      tacREWRITE [thmFST, thmSND]

recursionPAIR :: PairBCtxt thry => HOL cls thry HOLThm
recursionPAIR = cacheProof "recursionPAIR" ctxtPairB $
    prove "!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1" $
      tacGEN `_THEN` 
      tacEXISTS [str| \p. (PAIR':A->B->C) (FST p) (SND p) |] `_THEN`
      tacREWRITE [thmFST, thmSND]

inductPAIR :: PairBCtxt thry => HOL cls thry HOLThm
inductPAIR = cacheProof "inductPAIR" ctxtPairB $
    prove "!P. (!x y. P (x,y)) ==> !p. P p" $
      _REPEAT tacSTRIP `_THEN`
      tacGEN_REWRITE convRAND [ruleGSYM thmPAIR] `_THEN`
      _FIRST_ASSUM tacMATCH_ACCEPT

data Definitions = Definitions !(Map Text HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''Definitions

getDefinitions :: Query Definitions [HOLThm]
getDefinitions =
    do (Definitions m) <- ask
       return $! mapElems m

getDefinition' :: Text -> Query Definitions (Maybe HOLThm)
getDefinition' lbl =
    do (Definitions m) <- ask
       return $! mapLookup lbl m

addDefinition :: Text -> HOLThm -> Update Definitions ()
addDefinition lbl th =
    do (Definitions m) <- get
       put (Definitions (mapInsert lbl th m))

addDefinitions :: [(Text, HOLThm)] -> Update Definitions ()
addDefinitions m =
    put (Definitions (mapFromList m))

makeAcidic ''Definitions 
    ['getDefinitions, 'getDefinition', 'addDefinition, 'addDefinitions]


newDefinition :: (PairBCtxt thry, HOLTermRep tm Theory thry) 
              => Text -> tm -> HOL Theory thry HOLThm
newDefinition lbl ptm =
    do acid <- openLocalStateHOL (Definitions mapEmpty)
       qth <- queryHOL acid (GetDefinition' lbl)
       case qth of
         Just th ->
               closeAcidStateHOL acid >> return th
         Nothing -> noteHOL "newDefinition" $
              do defs <- queryHOL acid GetDefinitions
                 closeAcidStateHOL acid
                 tm <- toHTm ptm
                 let (avs, def) = stripForall tm
                 (do(th, th') <- tryFind (\ th -> do th' <- rulePART_MATCH Just
                                                              th def
                                                     return (th, th')) defs
                    void . rulePART_MATCH Just th' . snd . stripForall $ 
                             concl th
                    warn True "Benign redefinition"
                    th'' <- ruleGEN_ALL =<< ruleGENL avs th'
                    acid' <- openLocalStateHOL (Definitions mapEmpty)
                    updateHOL acid' (AddDefinition lbl th'')
                    createCheckpointAndCloseHOL acid'
                    return th'')
                  <|> (do (l, r) <- liftMaybe "newDefinition: Not an equation" $
                                      destEq def
                          let (fn, args) = stripComb l
                          args' <- mapM depair args
                          let (gargs, reps) = (id `ffComb` unions) $ unzip args'
                              l' = fromRight $ listMkComb fn gargs
                          r' <- liftO $ subst reps r
                          th1 <- D.newDefinition lbl =<< mkEq l' r'
                          let slist = zip gargs args
                          th2 <- liftM (fromJust . primINST slist) $ 
                                   ruleSPEC_ALL th1
                          xreps <- liftO $ mapM (subst slist . snd) reps
                          let conv = convPURE_REWRITE [thmFST, thmSND]
                          threps <- mapM (\ x -> do x' <- runConv conv x
                                                    liftO $ ruleSYM x') xreps
                          rth <- runConv (convSUBS threps) r
                          th3 <- liftO $ primTRANS th2 =<< ruleSYM rth
                          th4 <- ruleGEN_ALL =<< ruleGENL avs th3
                          acid' <- openLocalStateHOL (Definitions mapEmpty)
                          updateHOL acid' (AddDefinition lbl th4)
                          createCheckpointAndCloseHOL acid'
                          return th4)
  where depair :: HOLTerm -> HOL cls thry (HOLTerm, [(HOLTerm, HOLTerm)])
        depair x =
            do gv <- genVar $ typeOf x
               args' <- depairRec gv x
               return (gv, args')
          where depairRec :: HOLTerm -> HOLTerm 
                          -> HOL cls thry [(HOLTerm, HOLTerm)]
                depairRec gv arg = 
                    (do (l, r) <- liftO $ destBinary "," arg
                        l' <- liftM1 depairRec (listMkIComb "FST" [gv]) l
                        r' <- liftM1 depairRec (listMkIComb "SND" [gv]) r
                        return $! l' ++ r')
                    <|> return [(arg, gv)]

getDefinition :: Text -> HOL cls thry HOLThm
getDefinition lbl =
    do acid <- openLocalStateHOL (Definitions mapEmpty)
       qth <- queryHOL acid (GetDefinition' lbl)
       closeAcidStateHOL acid
       liftMaybe ("getDefinition: definition for " ++ show lbl ++ 
                  " not found.") qth
            
defCURRY' :: PairBCtxt thry => HOL Theory thry HOLThm
defCURRY' = newDefinition "CURRY"
    [str| CURRY(f:A#B->C) x y = f(x,y) |]

defUNCURRY' :: PairBCtxt thry => HOL Theory thry HOLThm
defUNCURRY' = newDefinition "UNCURRY"
    [str| !f x y. UNCURRY(f:A->B->C)(x,y) = f x y |]

defPASSOC' :: PairBCtxt thry => HOL Theory thry HOLThm
defPASSOC' = newDefinition "PASSOC"
    [str| !f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z) |]
