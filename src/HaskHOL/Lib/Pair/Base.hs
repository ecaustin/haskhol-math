{-# LANGUAGE ScopedTypeVariables #-}
module HaskHOL.Lib.Pair.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)

import HaskHOL.Lib.Pair.A
import HaskHOL.Lib.Pair.B
import HaskHOL.Lib.Pair.C


defCURRY :: PairCCtxt thry => HOL cls thry HOLThm
defCURRY = cacheProof "defCURRY" ctxtPairC $ getDefinition "CURRY"

defUNCURRY :: PairCCtxt thry => HOL cls thry HOLThm
defUNCURRY = cacheProof "defUNCURRY" ctxtPairC $ getDefinition "UNCURRY"

defPASSOC :: PairCCtxt thry => HOL cls thry HOLThm
defPASSOC = cacheProof "defPASSOC" ctxtPairC $ getDefinition "PASSOC"

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
                            
convGEQ :: PairACtxt thry => Conversion cls thry
convGEQ = convREWR (ruleGSYM defGEQ)

ruleDEGEQ :: PairACtxt thry => HOLThm -> HOL cls thry HOLThm
ruleDEGEQ = ruleCONV (convREWR defGEQ)

ruleGABS :: PairCCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleGABS = liftM1 ruleMATCH_MP ruleGABS_pth
  where ruleGABS_pth :: PairCCtxt thry => HOL cls thry HOLThm
        ruleGABS_pth = cacheProof "ruleGABS_pth" ctxtPairC $
            prove "(?) P ==> P (GABS P)" $
              tacSIMP [defGABS, axSELECT, axETA]

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

convGEN_BETA :: PairCCtxt thry => Conversion cls thry
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
