{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module HaskHOL.Lib.Pair.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)
import qualified HaskHOL.Deductive as D (getDefinition, newDefinition)

tmA, tmB, tmX, tmY :: BaseCtxt thry => HOL cls thry HOLTerm
tmA = serve [baseQQ| a:A |]
tmB = serve [baseQQ| b:B |]
tmX = serve [baseQQ| x:A |]
tmY = serve [baseQQ| y:B |]

tyDefProd :: HOL cls thry HOLThm
tyDefProd = unsafeCacheProof "tyDefProd" $ getTypeDefinition "prod"

defCOMMA :: HOL cls thry HOLThm
defCOMMA = unsafeCacheProof "defCOMMA" $ D.getDefinition ","

defMK_PAIR :: HOL cls thry HOLThm
defMK_PAIR = unsafeCacheProof "defMK_PAIR" $ D.getDefinition "mk_pair"

defFST :: HOL cls thry HOLThm
defFST = unsafeCacheProof "defFST" $ D.getDefinition "FST"

defSND :: HOL cls thry HOLThm
defSND = unsafeCacheProof "defSND" $ D.getDefinition "SND"

-- stage2
thmPAIR_EXISTS :: TriviaCtxt thry => HOL cls thry HOLThm
thmPAIR_EXISTS = unsafeCacheProof "thmPAIR_EXISTS" $
    prove [txt| ? x. ? (a:A) (b:B). x = mk_pair a b |] tacMESON_NIL

-- stage3
thmREP_ABS_PAIR :: TriviaCtxt thry => HOL cls thry HOLThm
thmREP_ABS_PAIR = unsafeCacheProof "thmREP_ABS_PAIR" $
    prove [txt| !(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = 
                              mk_pair x y |] $
      tacMESON [tyDefProd]

thmPAIR_SURJECTIVE :: BoolCtxt thry => HOL cls thry HOLThm
thmPAIR_SURJECTIVE = unsafeCacheProof "thmPAIR_SURJECTIVE" $
    do (th1, th2) <- ruleCONJ_PAIR tyDefProd
       prove [txt| !p:A#B. ?x y. p = x,y |] $
         tacGEN `_THEN` tacREWRITE [defCOMMA] `_THEN`
         tacMP (ruleSPEC [txt| REP_prod p :A->B->bool |] th2) `_THEN` 
         tacREWRITE [th1] `_THEN`
         _DISCH_THEN (_X_CHOOSE_THEN tmA 
                      (_X_CHOOSE_THEN tmB tacMP)) `_THEN`
         _DISCH_THEN (tacMP . 
                      ruleAP_TERM [txt| ABS_prod:(A->B->bool)->A#B |]) `_THEN`
         tacREWRITE [th1] `_THEN` _DISCH_THEN tacSUBST1 `_THEN`
         _MAP_EVERY tacEXISTS [tmA, tmB] `_THEN` tacREFL

thmPAIR_EQ :: TriviaCtxt thry => HOL cls thry HOLThm
thmPAIR_EQ = unsafeCacheProof "thmPAIR_EQ" $
    do prove [txt| !(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\ (y = b) |] $
         _REPEAT tacGEN `_THEN` tacEQ `_THENL`
         [ tacREWRITE [defCOMMA] `_THEN`
           _DISCH_THEN (tacMP . 
                        ruleAP_TERM [txt| REP_prod:A#B->A->B->bool |]) `_THEN`
           tacREWRITE [thmREP_ABS_PAIR] `_THEN` 
           tacREWRITE [defMK_PAIR, thmFUN_EQ]
         , _ALL
         ] `_THEN`
         tacMESON_NIL

thmFST :: TriviaCtxt thry => HOL cls thry HOLThm
thmFST = unsafeCacheProof "thmFST" .
    prove [txt| !(x:A) (y:B). FST(x,y) = x |] $
      _REPEAT tacGEN `_THEN` tacREWRITE[defFST] `_THEN`
      tacMATCH_MP thmSELECT_UNIQUE `_THEN` tacGEN `_THEN` tacBETA `_THEN`
      tacREWRITE [thmPAIR_EQ] `_THEN` tacEQ `_THEN`
      tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
      tacEXISTS tmY `_THEN` tacASM_REWRITE_NIL

thmSND :: TriviaCtxt thry => HOL cls thry HOLThm
thmSND = unsafeCacheProof "thmSND" .
    prove [txt| !(x:A) (y:B). SND(x,y) = y |] $
      _REPEAT tacGEN `_THEN` tacREWRITE [defSND] `_THEN`
      tacMATCH_MP thmSELECT_UNIQUE `_THEN` tacGEN `_THEN` tacBETA `_THEN`
      tacREWRITE [thmPAIR_EQ] `_THEN` tacEQ `_THEN`
      tacSTRIP `_THEN` tacASM_REWRITE_NIL `_THEN`
      tacEXISTS tmX `_THEN` tacASM_REWRITE_NIL

thmPAIR :: TriviaCtxt thry => HOL cls thry HOLThm
thmPAIR = unsafeCacheProof "thmPAIR" .
    prove [txt| !x:A#B. FST x,SND x = x |] $
      tacGEN `_THEN` 
      _X_CHOOSE_THEN tmA (_X_CHOOSE_THEN tmB tacSUBST1)
        (ruleSPEC [txt| x:A#B |] thmPAIR_SURJECTIVE) `_THEN`
      tacREWRITE [thmFST, thmSND]

data Definitions = Definitions !(Map Text HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''Definitions

getDefinitions :: Query Definitions (Map Text HOLThm)
getDefinitions =
    do (Definitions m) <- ask
       return m

addDefinition :: Text -> HOLThm -> Update Definitions ()
addDefinition lbl th =
    do (Definitions m) <- get
       put (Definitions (mapInsert lbl th m))

addDefinitions :: [(Text, HOLThm)] -> Update Definitions ()
addDefinitions m =
    put (Definitions (mapFromList m))

makeAcidic ''Definitions 
    ['getDefinitions, 'addDefinition, 'addDefinitions]


getDefs :: HOL cls thry (Map Text HOLThm)
getDefs =
    do acid <- openLocalStateHOL (Definitions mapEmpty)
       res <- queryHOL acid GetDefinitions
       closeAcidStateHOL acid
       return res

newDefinition :: (TriviaCtxt thry, HOLTermRep tm Theory thry)
              => (Text, tm) -> HOL Theory thry HOLThm
newDefinition (lbl, ptm) =
    do defs <- getDefs
       case mapAssoc lbl defs of
         Just th -> return th
         Nothing -> note "newDefinition" $
              do tm <- toHTm ptm
                 let (avs, def) = stripForall tm
                 (do(c, th') <- tryFind (\ th@(Thm _ c) -> 
                                          do th' <- rulePART_MATCH return th def
                                             return (c, th')) $ mapElems defs
                    void . rulePART_MATCH return th' . snd $ stripForall c
                    warn True "Benign redefinition"
                    th'' <- ruleGEN_ALL $ ruleGENL avs th'
                    acid' <- openLocalStateHOL (Definitions mapEmpty)
                    updateHOL acid' (AddDefinition lbl th'')
                    closeAcidStateHOL acid'
                    return th'')
                  <|> (do (l, r) <- destEq def
                          let (fn, args) = stripComb l
                          args' <- mapM depair args
                          let (gargs, reps) = (id `ffComb` unions) $ unzip args'
                          l' <- listMkComb fn gargs
                          r' <- subst reps r
                          edef <- mkEq l' r'
                          th1 <- D.newDefinition (lbl, edef)
                          let slist = zip gargs args
                          th2 <- primINST slist $ ruleSPEC_ALL th1
                          xreps <- mapM (subst slist . snd) reps
                          let conv = convPURE_REWRITE [thmFST, thmSND]
                          threps <- mapM (ruleSYM . runConv conv) xreps
                          rth <- runConv (convSUBS threps) r
                          th3 <- primTRANS th2 $ ruleSYM rth
                          th4 <- ruleGEN_ALL $ ruleGENL avs th3
                          acid' <- openLocalStateHOL (Definitions mapEmpty)
                          updateHOL acid' (AddDefinition lbl th4)
                          closeAcidStateHOL acid'
                          return th4)
  where depair :: HOLTerm -> HOL cls thry (HOLTerm, [(HOLTerm, HOLTerm)])
        depair x =
            do gv <- genVar $ typeOf x
               args' <- depairRec gv x
               return (gv, args')
          where depairRec :: HOLTerm -> HOLTerm 
                          -> HOL cls thry [(HOLTerm, HOLTerm)]
                depairRec gv arg = 
                    (do (l, r) <- destBinary "," arg
                        l' <- flip depairRec l =<< listMkIComb "FST" [gv]
                        r' <- flip depairRec r =<< listMkIComb "SND" [gv]
                        return $! l' ++ r')
                    <|> return [(arg, gv)]
    

-- stage4
recursionPAIR :: TriviaCtxt thry => HOL cls thry HOLThm
recursionPAIR = unsafeCacheProof "recursionPAIR" .
    prove [txt| !PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1 |] $
      tacGEN `_THEN` 
      tacEXISTS [txt| \p. (PAIR':A->B->C) (FST p) (SND p) |] `_THEN`
      tacREWRITE [thmFST, thmSND]

inductPAIR :: TriviaCtxt thry => HOL cls thry HOLThm
inductPAIR = unsafeCacheProof "inductPAIR" .
    prove [txt| !P. (!x y. P (x,y)) ==> !p. P p |] $
      _REPEAT tacSTRIP `_THEN`
      tacGEN_REWRITE convRAND [ruleGSYM thmPAIR] `_THEN`
      _FIRST_ASSUM tacMATCH_ACCEPT
                        
