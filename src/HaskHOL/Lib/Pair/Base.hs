{-# LANGUAGE ScopedTypeVariables #-}
module HaskHOL.Lib.Pair.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition)
import qualified HaskHOL.Deductive as D (newDefinition)

-- Stage 1
defLET' :: BoolCtxt thry => HOL Theory thry HOLThm
defLET' = D.newDefinition "LET"
    [str| LET (f:A->B) x = f x |]

defLET_END' :: BoolCtxt thry => HOL Theory thry HOLThm
defLET_END' = D.newDefinition "LET_END"
    [str| LET_END (t:A) = t |]

defGABS' :: BoolCtxt thry => HOL Theory thry HOLThm
defGABS' = D.newDefinition "GABS"
    [str| GABS (P:A->bool) = (@) P |]

defGEQ' :: BoolCtxt thry => HOL Theory thry HOLThm
defGEQ' = D.newDefinition "GEQ"
    [str| GEQ a b = (a:A = b) |]

def_SEQPATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_SEQPATTERN' = D.newDefinition "_SEQPATTERN"
    [str| _SEQPATTERN = \ r s x. if ? y. r x y then r x else s x |]

def_UNGUARDED_PATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_UNGUARDED_PATTERN' = D.newDefinition "_UNGUARDED_PATTERN"
    [str| _UNGUARDED_PATTERN = \ p r. p /\ r |]

def_GUARDED_PATTERN' :: BoolCtxt thry => HOL Theory thry HOLThm
def_GUARDED_PATTERN' = D.newDefinition "_GUARDED_PATTERN"
    [str| _GUARDED_PATTERN = \ p g r. p /\ g /\ r |]

def_MATCH' :: BoolCtxt thry => HOL Theory thry HOLThm
def_MATCH' = D.newDefinition "_MATCH"
    [str| _MATCH =  \ e r. if (?!) (r e) then (@) (r e) else @ z. F |]

def_FUNCTION' :: BoolCtxt thry => HOL Theory thry HOLThm
def_FUNCTION' = D.newDefinition "_FUNCTION"
    [str| _FUNCTION = \ r x. if (?!) (r x) then (@) (r x) else @ z. F |]

defMK_PAIR' :: BoolCtxt thry => HOL Theory thry HOLThm
defMK_PAIR' = D.newDefinition "mk_pair"
    [str| mk_pair (x:A) (y:B) = \ a b. (a = x) /\ (b = y) |]

-- stage2
thmPAIR_EXISTS' :: PairACtxt thry => HOL cls thry HOLThm
thmPAIR_EXISTS' = prove "? x. ? (a:A) (b:B). x = mk_pair a b" tacMESON_NIL

tyDefProd' :: PairACtxt thry => HOL Theory thry HOLThm
tyDefProd' = newTypeDefinition "prod" "ABS_prod" "REP_prod" thmPAIR_EXISTS'

defCOMMA' :: BoolCtxt thry => HOL Theory thry HOLThm
defCOMMA' = D.newDefinition ","
    [str| ((x:A), (y:B)) = ABS_prod(mk_pair x y) |]

defFST' :: BoolCtxt thry => HOL Theory thry HOLThm
defFST' = D.newDefinition "FST"
    [str| FST (p:A#B) = @ x. ? y. p = (x, y) |]

defSND' :: BoolCtxt thry => HOL Theory thry HOLThm
defSND' = D.newDefinition "SND"
    [str| SND (p:A#B) = @ y. ? x. p = (x, y) |]

-- stage3
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

-- stage4
type ProjectionState = HOLRef ProjectionCache
data ProjectionCache = ProjectionCache !(Map Text [HOLThm]) deriving Typeable

createProjections :: ClassicCtxt thry => ProjectionState 
                  -> Text -> HOL cls thry [HOLThm]
createProjections ref conname =
    do (ProjectionCache projs) <- readHOLRef ref
       case mapLookup conname projs of
         Just ths -> return ths
         _ ->
              do genty <- getConstType conname
                 let conty = fromJust . liftM (fst . destTypeOp) $
                               (liftM fst . destType) =<< 
                                 repeatM (liftM snd . destFunTy) genty
                 itys <- getIndDefs
                 (_, _, rth) <- liftMaybe ("createProjections: not in " ++ 
                                           "inductive type store") $ 
                                  mapLookup conty itys
                 sth <- ruleSPEC_ALL rth
                 let (evs, bod) = stripExists $ concl sth
                     cjs = conjuncts bod
                     (ourcj, n) = fromJust . findM (\ (x, _) -> 
                          do x' <- rand =<< (lHand . snd $ stripForall x)
                             (x'', _) <- destConst . fst $ stripComb x'
                             return $ x'' == conname) $ zip cjs [0..]
                     (avs, eqn) = stripForall ourcj
                     (con', args) = stripComb . fromJust $ rand eqn
                     (aargs, zargs) = fromJust $ chopList (length avs) args
                 gargs <- mapM (genVar . typeOf) zargs
                 gcon <- genVar =<< foldrM (mkFunTy . typeOf) 
                            (typeOf . fromJust $ rand eqn) avs
                 let btm = fromRight $ listMkAbs (aargs++gargs) =<< listMkComb gcon avs
                     bth = fromJust $ primINST [(con', btm)] sth
                 cths <- ruleCONJUNCTS #<< 
                           primASSUME (snd . stripExists $ concl bth)
                 let cth = cths !! n
                 dth <- ruleCONV (funpow (length avs) convBINDER 
                          (convRAND convBETAS)) cth
                 let etm = fromJust $ rator =<< 
                             lHand (snd . stripForall $ concl dth)
                 eth <- ruleSIMPLE_EXISTS etm dth
                 fth <- liftM (rulePROVE_HYP bth) $ 
                          foldrM ruleSIMPLE_CHOOSE eth evs
                 let zty = typeOf . fromJust . rand . snd . stripForall $ 
                             concl dth
                     mkProjector a = 
                         let ity = typeOf a
                             atm = fromRight $ listMkAbs avs a
                             th1 = fromJust $
                                     rulePINST [(zty, ity)] [(gcon, atm)] fth in
                           do th2 <- ruleSPEC_ALL =<< ruleSELECT =<< 
                                       ruleBETA th1
                              liftO $ ruleSYM th2
                 ths <- mapM mkProjector avs
                 writeHOLRef ref $ ProjectionCache (mapInsert conname ths projs)
                 return ths
                            
convGEQ_pth' :: HOL cls thry HOLThm
convGEQ_pth' = ruleGSYM defGEQ'

convGEQ' :: HOL cls thry HOLThm -> Conversion cls thry
convGEQ' pth' = convREWR pth'

ruleDEGEQ_pth' :: HOL cls thry HOLThm
ruleDEGEQ_pth' = convREWR defGEQ'

ruleDEGEQ' :: HOL cls thry HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleDEGEQ' pth' = ruleCONV pth'

ruleGABS_pth' :: HOL cls thry HOLThm
ruleGABS_pth' =
    prove "(?) P ==> P (GABS P)" $ tacSIMP [defGABS, axSELECT, axETA]


ruleGABS' :: HOL cls thry HOLThm -> HOLThm -> HOL cls thry HOLThm
ruleGABS' pth' = liftM1 ruleMATCH_MP pth'
            

createIteratedProjections :: ClassicCtxt thry
                          => ProjectionState -> HOLTerm 
                          -> HOL cls thry [HOLThm]
createIteratedProjections ref tm
    | null $ frees tm = return []
    | isVar tm = return [primREFL tm]
    | otherwise =
      let (con, _) = stripComb tm in
        do prjths <- createProjections ref . fst . fromJust $ destConst con
           let atm = fromJust $ rand =<< rand (concl $ head prjths)
           instn <- liftO $ termMatch [] atm tm
           arths <- mapM (ruleINSTANTIATE instn) prjths
           ths <- mapM (\ arth -> 
                    do sths <- createIteratedProjections ref #<< 
                                 lHand (concl arth)
                       mapM (ruleCONV (convRAND $ convSUBS [arth])) sths) arths
           return $! unions ths

convGEN_BETA :: Conversion cls thry
convGEN_BETA = Conv $ \ tm ->
    runConv convBETA tm
    <|> noteHOL "convGEN_BETA"
          (do (l, r) <- liftMaybe "not a combination." $ destComb tm
              (vstr, bod) <- liftMaybe "rator not an abstraction." $ destGAbs l
              instn <- liftO $ termMatch [] vstr r
              ref <- newHOLRef $ ProjectionCache mapEmpty
              prjs <- createIteratedProjections ref vstr
              bth <- runConv (convSUBS prjs) bod
              gv <- genVar $ typeOf vstr
              bod' <- liftO $ subst [(vstr, gv)] =<< rand (concl bth)
              let pat = fromRight $ mkAbs gv bod'
              th1 <- runConv convBETA #<< mkComb pat vstr
              let th2 = fromRight $ primTRANS th1 =<< ruleSYM bth
                  avs = fst . stripForall . fromJust $ body =<< rand l
              th3 <- ruleGENL avs th2
              efn <- genVar $ typeOf pat
              efn' <- mkExists efn #<< subst [(pat, efn)] (concl th3)
              th4 <- ruleEXISTS efn' pat th3
              th5 <- ruleCONV (funpow (length avs + 1) convBINDER convGEQ) th4
              th6 <- ruleCONV convBETA =<< ruleGABS th5
              ruleINSTANTIATE instn =<< ruleDEGEQ =<< ruleSPEC_ALL th6) 
