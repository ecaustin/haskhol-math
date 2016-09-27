{-|
  Module:    HaskHOL.Lib.IndTypes
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.IndTypes
    ( IndTypesCtxt
    , ctxtIndTypes
    , indTypes
    , inductSUM
    , recursionSUM
    , defOUTL
    , defOUTR
    , inductOPTION
    , recursionOPTION
    , inductLIST
    , recursionLIST
    , defISO
    , thmISO_REFL
    , thmISO_FUN
    , thmISO_USAGE
    , defineType
    , getType
    , convFORALL_UNWIND
    , convMATCH_ONEPATTERN
    , convMATCH_ONEPATTERN_TRIV
    , convMATCH_SEQPATTERN
    , convMATCH_SEQPATTERN_TRIV
    , Base.basicRectypeNet
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Recursion

import HaskHOL.Lib.IndTypes.Pre (parseInductiveTypeSpecification)
import qualified HaskHOL.Lib.IndTypes.Pre2 as Pre (defineTypeRaw)

import qualified HaskHOL.Lib.IndTypes.Base as Base
import HaskHOL.Lib.IndTypes.Context
import HaskHOL.Lib.IndTypes.PQ

tmT :: BoolCtxt thry => HOL cls thry HOLTerm
tmT = serve [bool| T |]


defOUTL :: IndTypesCtxt thry => HOL cls thry HOLThm
defOUTL = cacheProof "defOUTL" ctxtIndTypes $ getRecursiveDefinition "OUTL"

defOUTR :: IndTypesCtxt thry => HOL cls thry HOLThm
defOUTR = cacheProof "defOUTR" ctxtIndTypes $ getRecursiveDefinition "OUTR"

inductSUM :: IndTypesCtxt thry => HOL cls thry HOLThm
inductSUM = cacheProof "inductSUM" ctxtIndTypes $
    do defs <- getIndDefs
       (_, th, _) <- mapAssoc "sum" defs
       return th

recursionSUM :: IndTypesCtxt thry => HOL cls thry HOLThm
recursionSUM = cacheProof "recursionSUM" ctxtIndTypes $
    do defs <- getIndDefs
       (_, _, th) <- mapAssoc "sum" defs
       return th

defISO :: IndTypesCtxt thry => HOL cls thry HOLThm
defISO = cacheProof "defISO" ctxtIndTypes $ getDefinition "ISO"

indDefOption :: IndTypesCtxt thry => HOL cls thry (HOLThm, HOLThm)
indDefOption =
    do defs <- getIndDefs
       (_, th1, th2) <- mapAssoc "option" defs
       return (th1, th2)

inductOPTION :: IndTypesCtxt thry => HOL cls thry HOLThm
inductOPTION = cacheProof "inductOPTION" ctxtIndTypes $
    liftM fst indDefOption

recursionOPTION :: IndTypesCtxt thry => HOL cls thry HOLThm
recursionOPTION = cacheProof "recursionOPTION" ctxtIndTypes $
    liftM snd indDefOption

inductLIST :: IndTypesCtxt thry => HOL cls thry HOLThm
inductLIST = cacheProof "inductLIST" ctxtIndTypes $
    do defs <- getIndDefs
       (_, th, _) <- mapAssoc "list" defs
       return th

recursionLIST :: IndTypesCtxt thry => HOL cls thry HOLThm
recursionLIST = cacheProof "recursionLIST" ctxtIndTypes $
    do defs <- getIndDefs
       (_, _, th) <- mapAssoc "list" defs
       return th

thmISO_REFL :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_REFL = cacheProof "thmISO_REFL" ctxtIndTypes $
    prove [txt| ISO (\x:A. x) (\x. x) |] $ tacREWRITE [defISO]

thmISO_FUN :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_FUN = cacheProof "thmISO_FUN" ctxtIndTypes .
    prove [txt| ISO (f:A->A') f' /\ ISO (g:B->B') g'
                ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a))) |] $
      tacREWRITE [defISO, thmFUN_EQ] `_THEN` tacMESON_NIL

thmISO_USAGE :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_USAGE = cacheProof "thmISO_USAGE" ctxtIndTypes .
    prove [txt| ISO f g
                ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
                    (!P. (?x. P x) <=> (?x. P(g x))) /\
                    (!a b. (a = g b) <=> (f a = b)) |] $
      tacREWRITE [defISO, thmFUN_EQ] `_THEN` tacMESON_NIL

proveITT_pth :: IndTypesCtxt thry => HOL cls thry HOLThm
proveITT_pth = cacheProof "proveITT_pth" ctxtIndTypes .
    prove [txt| (?) P ==> (c = (@)P) ==> P c |] $
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacDISCH `_THEN` _DISCH_THEN tacSUBST1 `_THEN`
      tacMATCH_MP axSELECT `_THEN` _POP_ASSUM tacACCEPT

defineType :: IndTypesCtxt thry => Text -> HOL Theory thry (HOLThm, HOLThm)
defineType s =
    do acid <- openLocalStateHOL (Base.InductiveTypes mapEmpty)
       indTys <- queryHOL acid Base.GetInductiveTypes
       closeAcidStateHOL acid
       let s' = head $ textWords s
       (mapAssoc s' indTys <|>
         (do ctxt <- parseContext
             defspec <- parseInductiveTypeSpecification ctxt s
             let newtypes = map fst defspec
                 constructors = foldr ((++) . map fst) [] $ map snd defspec
             when ((length (setify newtypes)) /= length newtypes) $
               fail "defineType: multiple definitions of a type."
             when ((length (setify constructors)) /= length constructors) $
               fail "defineType: multiple instances of a constructor."
             cond1 <- mapM (can (getTypeArity <=< destVarType)) newtypes
             cond2 <- mapM (can getConstType) constructors
             if or cond1
                then do t <- findM (can getTypeArity) =<< 
                               mapM destVarType newtypes
                        fail $ "defineType: type " ++ show t ++ 
                               " already defined."
                else if or cond2
                     then do t <- findM (can getConstType) constructors
                             fail $ "defineType: constant " ++ show t ++ 
                                    " already defined."
                     else do retval <- defineTypeRaw defspec
                             acid' <- openLocalStateHOL 
                                        (Base.InductiveTypes mapEmpty)
                             updateHOL acid' (Base.AddInductiveType s' retval)
                             closeAcidStateHOL acid'
                             return retval))

getType :: Text -> HOL cls thry (HOLThm, HOLThm)
getType name =
    do acid <- openLocalStateHOL (Base.InductiveTypes mapEmpty)
       qth <- queryHOL acid (Base.GetInductiveType name)
       closeAcidStateHOL acid
       case qth of
         Just res -> return res
         _ -> fail $ "getType: type " ++ show name ++ " not found."


defineTypeRaw :: IndTypesCtxt thry
              => [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw def =
    let newtys = map fst def
        truecons = foldr (++) [] $ map (map fst . snd) def in
      do (p, ith0, rth0) <- defineTypeNested def
         let (avs, etm) = stripForall $ concl rth0
             allcls = conjuncts . snd $ stripExists etm
         (relcls, _) <- trySplitAt (length truecons) allcls
         gencons <- mapM (repeatM rator <=< rand . lHand . snd . stripForall) 
                      relcls
         cdefs <- map2M (\ s r -> do deftm <- mkEq (mkVar s $ typeOf r) r
                                     dth <- newDefinition (s, deftm)
                                     ruleSYM dth) truecons gencons
         tavs <- mkArgs "f" [] `fmap` mapM typeOf avs
         ith1 <- ruleSUBS cdefs ith0
         rth1 <- ruleGENL tavs . ruleSUBS cdefs =<< ruleSPECL tavs rth0
         let retval = (p, ith1, rth1)
         newentries <- mapM (\s -> do s' <- destVarType s
                                      return (s', retval)) newtys
         mapM_ addIndDef newentries
         mapM_ Base.extendRectypeNet newentries
         return (ith1, rth1)

defineTypeNested :: IndTypesCtxt thry 
                 => [(HOLType, [(Text, [HOLType])])] 
                 -> HOL Theory thry (Int, HOLThm, HOLThm)
defineTypeNested def =
    let n = length . foldr (++) [] $ map (map fst . snd) def
        newtys = map fst def
        utys = unions $ foldr (union . map snd . snd) [] def
        rectys = filter (isNested newtys) utys in
      if null rectys then do (th1, th2) <- defineTypeBasecase
                             return (n, th1, th2)
      else let nty = head (sort (\ t1 t2 -> t2 `occursIn` t1) rectys) in
             do (k, tyal, ncls, ith, rth) <- createAuxiliaryClauses nty
                cls <- mapM (modifyClause tyal) $ def ++ ncls
                (_, ith1, rth1) <- defineTypeNested cls
                xnewtys <- mapM (liftM (head . snd) . destType <=< typeOf) .
                                fst . stripExists . snd . stripForall $ 
                                  concl rth1
                xtyal <- mapM (\ ty -> 
                           do s <- destVarType ty
                              s' <- findM (\ t -> 
                                      do (t', _) <- destType t
                                         let (op, _) = destTypeOp t'
                                         return $! op == s) xnewtys
                              return (ty, s')) $ map fst cls
                ith0 <- primINST_TYPE xtyal ith
                rth0 <- primINST_TYPE xtyal rth
                (isoth, rclauses) <- proveInductiveTypesIsomorphic n k 
                                       (ith0, rth0) (ith1, rth1)
                irth3 <- ruleCONJ ith1 rth1
                vtylist <- foldrM (\ tm acc -> 
                                   do ty <- typeOf tm
                                      return $! insert ty acc) [] . variables $ 
                             concl irth3
                isoths <- ruleCONJUNCTS isoth
                isotys <- mapM (liftM (head . snd) . destType <=<
                                typeOf <=< lHand . concl) isoths
                let ctylist = filter (\ ty -> 
                                      any (\ t -> t `occursIn` ty) isotys) 
                                vtylist
                atylist <- foldrM (\ tm acc ->
                                   do tm' <- stripListM destFunTy tm
                                      return $! union tm' acc) [] ctylist
                isoths' <- mapM (liftTypeBijections isoths) $
                            filter (\ ty -> any (\ t -> t `occursIn` ty) isotys)
                              atylist
                cisoths <- mapM (ruleBETA <=< liftTypeBijections isoths') 
                             ctylist
                uisoths <- mapM ruleISO_USAGE cisoths
                visoths <- mapM (primASSUME . concl) uisoths
                irth3' <- ruleREWRITE_FUN_EQ visoths irth3
                irth4 <- foldrM rulePROVE_HYP irth3' uisoths
                isoths'' <- mapM ruleSIMPLE_ISO_EXPAND isoths'
                irth5 <- ruleREWRITE (rclauses : isoths'') irth4
                irth6 <- repeatM ruleSCRUB_ASSUMPTION irth5
                ncjs <- filterM (\ t -> 
                          do ts <- liftM (snd . stripComb) 
                                     (rand . lhs . snd $ stripForall t)
                             return $! any (\ v -> not $ isVar v) ts) =<< 
                          (liftM (conjuncts . snd . stripExists . snd . 
                                  stripForall) . rand $ concl irth6)
                dths <- mapM mkNewcon ncjs
                (ith6, rth6) <- ruleCONJ_PAIR =<< rulePURE_REWRITE dths irth6
                return (n, ith6, rth6)
  where ruleSCRUB_ASSUMPTION :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleSCRUB_ASSUMPTION th =
            let hyps = hyp th in
              do eqn <- findM (\ t -> 
                        do x <- lhs t
                           us <- mapM (\ u -> do u' <- rand u
                                                 return $! x `freeIn` u') hyps
                           return $! and us) hyps
                 (l, r) <- destEq eqn
                 th' <- ruleDISCH eqn th
                 ruleMP (primINST [(l, r)] th') (primREFL r)

        ruleSIMPLE_BETA :: ClassicCtxt thry => HOLThm 
                        -> HOL cls thry HOLThm
        ruleSIMPLE_BETA = 
            ruleGSYM <=< rulePURE_REWRITE [thmBETA, thmFUN_EQ]

        ruleISO_USAGE :: IndTypesCtxt thry => HOLThm 
                      -> HOL cls thry HOLThm
        ruleISO_USAGE = ruleMATCH_MP thmISO_USAGE

        ruleSIMPLE_ISO_EXPAND :: IndTypesCtxt thry => HOLThm 
                              -> HOL cls thry HOLThm
        ruleSIMPLE_ISO_EXPAND = ruleCONV (convREWR defISO)

        ruleREWRITE_FUN_EQ :: ClassicCtxt thry => [HOLThm] 
                           -> HOLThm 
                           -> HOL cls thry HOLThm
        ruleREWRITE_FUN_EQ thms thm =
            do ths <- foldrM (mkRewrites False) [] [thmFUN_EQ]
               net <- basicNet
               net' <- foldrM (netOfThm False) net ths
               ruleCONV (convCACHED_GENERAL_REWRITE Nothing True 
                           convTOP_DEPTH net' thms) thm

        defineTypeBasecase :: IndTypesCtxt thry
                           => HOL Theory thry (HOLThm, HOLThm)
        defineTypeBasecase =
            let addId _ = fst `fmap` (destVar $ genVar tyBool) in
              do def' <- mapM (return `ffCombM` (mapM (addId `ffCombM` return)))
                           def
                 Pre.defineTypeRaw def'

        mkNewcon :: PairCtxt thry => HOLTerm -> HOL Theory thry HOLThm
        mkNewcon tm =
            let (vs, bod) = stripForall tm in
              do rdeb <- rand =<< lhs bod
                 rdef <- listMkAbs vs rdeb
                 (newname, _) <- destVar $ genVar tyBool
                 def' <- mkEq (mkVar newname $ typeOf rdef) rdef
                 dth <- newDefinition (newname, def')
                 ruleSIMPLE_BETA dth

        createAuxiliaryClauses :: HOLType -> 
          HOL cls thry (Int, HOLTypeEnv, 
                        [(HOLType, [(Text, [HOLType])])], HOLThm, HOLThm)
        createAuxiliaryClauses nty = 
            do (id', _) <- destVar $ genVar tyBool
               (tycon, _) <- destType nty
               indTys <- getIndDefs
               (k, ith, rth) <- ((fst $ destTypeOp tycon) `mapAssoc` indTys) <?>
                                  ("definedType: Can't find definition " ++
                                   "for nested type: " ++ show tycon)
               let (evs, bod) = stripExists . snd . stripForall $ concl rth
               cjs <- mapM (lHand . snd . stripForall) $ conjuncts bod
               rtys <- mapM (liftM (head . snd) . (destType <=< typeOf)) evs
               tyins <- tryFind (\ vty -> typeMatch_NIL vty nty) rtys
               cjs' <- mapM (liftM (instFull tyins) . rand) =<< 
                         (fst `fmap` trySplitAt k cjs)
               mtys <- foldrM (\ tm acc -> 
                                do ty <- typeOf tm
                                   return $! insert ty acc) [] cjs'
               pcons <- mapM (\ ty -> 
                                filterM (\ t -> 
                                         do ty' <- typeOf t
                                            return $! ty' == ty) cjs') mtys
               cls' <- zip mtys `fmap` (mapM (mapM (recoverClause id')) pcons)
               tyal <- mapM (\ ty -> do (x, _) <- (destTypeOp . fst) `fmap` 
                                                  destType ty
                                        return (mkVarType (x `append` id'), ty)) mtys
               cls'' <- mapM (modifyType tyal `ffCombM` 
                              mapM (modifyItem tyal)) cls'
               th1 <- primINST_TYPE_FULL tyins ith
               th2 <- primINST_TYPE_FULL tyins rth
               return (k, tyal, cls'', th1, th2)

        recoverClause :: Text -> HOLTerm -> HOL cls thry (Text, [HOLType])
        recoverClause id' tm =
            let (con, args) = stripComb tm in
              do (x, _) <- destConst con
                 tys <- mapM typeOf args
                 return (x `append` id', tys)

        modifyClause :: HOLTypeEnv -> (HOLType, [(Text, [HOLType])]) 
                     -> HOL cls thry (HOLType, [(Text, [HOLType])])
        modifyClause alist (l, lis) =
            do lis' <- mapM (modifyItem alist) lis
               return (l, lis')

        modifyItem :: HOLTypeEnv -> (Text, [HOLType]) 
                   -> HOL cls thry (Text, [HOLType])
        modifyItem alist (s, l) =
            do l' <- mapM (modifyType alist) l
               return (s, l')

        modifyType :: HOLTypeEnv -> HOLType -> HOL cls thry HOLType
        modifyType alist ty =
            revAssoc ty alist <|>
              do (tycon, tyargs) <- destType ty
                 tyApp tycon =<< mapM (modifyType alist) tyargs

        isNested :: [HOLType] -> HOLType -> Bool
        isNested vs ty = not (isVarType ty) && 
                         not (null $ intersect (tyVars ty) vs)

proveInductiveTypesIsomorphic :: IndTypesCtxt thry 
                              => Int -> Int 
                              -> (HOLThm, HOLThm) 
                              -> (HOLThm, HOLThm) 
                              -> HOL cls thry (HOLThm, HOLThm)
proveInductiveTypesIsomorphic n k (ith0, rth0) (ith1, rth1) =
    do sth0 <- ruleSPEC_ALL rth0
       sth1 <- ruleSPEC_ALL rth1
       let (pevs0, pbod0) = stripExists $ concl sth0
           (pevs1, pbod1) = stripExists $ concl sth1
       (pcjs0, _) <- trySplitAt k $ conjuncts pbod0
       (pcjs1, _) <- trySplitAt k =<< 
                       (snd `fmap` (trySplitAt n $ conjuncts pbod1))
       (pcjs1', pcjs0') <- pairMapM (mapM grabType) (pcjs1, pcjs0)
       let tyal0 = setify $ zip pcjs1' pcjs0'
           tyal1 = map (\ (a, b) -> (b, a)) tyal0
       tyins0 <- mapM (\ f ->
                   do (domty, ranty) <- destFunTy $ typeOf f
                      l <- tysubst tyal0 domty
                      return (l, ranty)) pevs0
       tyins1 <- mapM (\ f ->
                   do (domty, ranty) <- destFunTy $ typeOf f
                      l <- tysubst tyal1 domty
                      return (l, ranty)) pevs1
       tth0 <- primINST_TYPE tyins0 sth0
       tth1 <- primINST_TYPE tyins1 sth1
       let (_, bod0) = stripExists $ concl tth0
           (_, bod1) = stripExists $ concl tth1
       (lcjs0, rcjs0) <- trySplitAt k . map (snd . stripForall) $ conjuncts bod0
       (lcjs1, rcjsx) <- trySplitAt k =<< ((map (snd . stripForall) . snd) `fmap`
                                     (trySplitAt n $ conjuncts bod1))
       rcjs1 <- mapM (\ t -> findM (clauseCorresponds t) rcjsx) rcjs0
       (insts0, insts1) <- unzip `fmap` 
                           map2M procClause (lcjs0++rcjs0) (lcjs1++rcjs1)
       uth0 <- ruleBETA $ primINST insts0 tth0
       uth1 <- ruleBETA $ primINST insts1 tth1
       (efvs0, sth0') <- ruleDE_EXISTENTIALIZE uth0
       (efvs1, sth1') <- ruleDE_EXISTENTIALIZE uth1
       efvs2 <- mapM (\ t1 -> findM (\ t2 ->
                  do t1' <- destType =<< typeOf t1
                     t2' <- destType =<< typeOf t2
                     return $! (head . tail $ snd t1') == 
                               (head $ snd t2')) efvs1) efvs0
       isotms <- map2M (\ ff gg -> listMkIComb "ISO" [ff, gg]) efvs0 efvs2
       ctm <- listMkConj isotms
       cth1 <- runConv (convISO_EXPAND) ctm
       ctm1 <- rand $ concl cth1
       let cjs = conjuncts ctm1
           eee = map (\ x -> x `mod` 2 == 0) [0..(length cjs -1)]
           (cjs1, cjs2) = partition fst $ zip eee cjs
       ctm2 <- mkConj (listMkConj $ map snd cjs1) =<< listMkConj (map snd cjs2)
       let ruleDETRIV = ruleTRIV_ANTE <=< ruleREWRITE [sth0', sth1']
       jth0 <- do itha <- ruleSPEC_ALL ith0
                  icjs <- conjuncts `fmap` (rand $ concl itha)
                  cinsts <- mapM (\ tm -> tryFind (\ vtm ->
                                   termMatch [] vtm tm) icjs) =<< 
                                     conjuncts `fmap` (rand ctm2)
                  let tvs = (fst . stripForall $ concl ith0) \\
                                 (foldr (\ (_, x, _) -> union (map snd x)) [] 
                                    cinsts)
                  ctvs <- mapM (\ p ->
                            do (_, tys) <- destType =<< typeOf p
                               x <- mkVar "x" $ head tys
                               x' <- mkAbs x tmT
                               return (x', p)) tvs
                  ithas <- foldrM ruleINSTANTIATE itha cinsts
                  ruleDETRIV $ primINST ctvs ithas
       jth1 <- do itha <- ruleSPEC_ALL ith1
                  icjs <- conjuncts `fmap` (rand $ concl itha)
                  cinsts <-mapM (\ tm -> tryFind (\ vtm ->
                                   termMatch [] vtm tm) icjs) =<< 
                                     liftM conjuncts (lHand ctm2)
                  let tvs = (fst . stripForall $ concl ith1) \\
                                 (foldr (\ (_, x, _) -> union (map snd x)) []
                                    cinsts)
                  ctvs <- mapM (\ p ->
                            do (_, tys) <- destType =<< typeOf p
                               x <- mkVar "x" $ head tys
                               x' <- mkAbs x tmT
                               return (x', p)) tvs
                  ithas <- foldrM ruleINSTANTIATE itha cinsts
                  ruleDETRIV $ primINST ctvs ithas
       cths3_5 <- ruleCONJUNCTS jth0
       cths4 <- (map2M ruleCONJ) cths3_5 =<< ruleCONJUNCTS jth1
       cths5 <- mapM (rulePURE_ONCE_REWRITE [ruleGSYM defISO]) cths4
       cth6 <- foldr1M ruleCONJ cths5
       cth7 <- ruleCONJ sth0' sth1'
       return (cth6, cth7)
  where ruleTRIV_ANTE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleTRIV_ANTE th =
            let tm = concl th in
              if isImp tm
              then do (ant, _) <- destImp $ concl th
                      let cjs = conjuncts ant
                      cths <- mapM (runConv convTRIV_IMP) cjs
                      ruleMP th =<< foldr1M ruleCONJ cths
              else return th
          where convTRIV_IMP :: BoolCtxt thry => Conversion cls thry
                convTRIV_IMP = Conv $ \ tm ->
                    let (avs, bod) = stripForall tm in
                      do bth <- 
                             if isEq bod 
                             then primREFL $ rand bod
                             else do (ant, con) <- destImp bod
                                     ants <- ruleCONJUNCTS $ primASSUME ant
                                     ith <- runConv (convSUBS ants) $ lhs con
                                     ruleDISCH ant ith
                         ruleGENL avs bth
   
        convISO_EXPAND :: IndTypesCtxt thry => Conversion cls thry
        convISO_EXPAND = convPURE_ONCE_REWRITE [defISO]

        ruleDE_EXISTENTIALIZE :: IndTypesCtxt thry => HOLThm 
                              -> HOL cls thry ([HOLTerm], HOLThm)
        ruleDE_EXISTENTIALIZE th =
            if not . isExists $ concl th then return ([], th)
            else do th1 <- ruleMATCH_MP proveITT_pth th
                    v1 <- rand =<< rand (concl th1)
                    gv <- genVar $ typeOf v1
                    th2 <- ruleCONV convBETA =<< ruleUNDISCH =<< 
                             primINST [(v1, gv)] th1
                    (vs, th3) <- ruleDE_EXISTENTIALIZE th2
                    return (gv:vs, th3)

        procClause :: HOLTerm -> HOLTerm 
                   -> HOL cls thry ((HOLTerm, HOLTerm), (HOLTerm, HOLTerm))
        procClause tm0 tm1 =
            do (l0, r0) <- destEq tm0
               (l1, r1) <- destEq tm1
               let (vc0, wargs0) = stripComb r0
               (_, vargs0) <- stripComb `fmap` rand l0
               gargs0 <- mapM (genVar . typeOf) wargs0
               nestf0 <- mapM (\ a -> can (findM (\ t -> 
                               do t' <- rand t
                                  return $! isComb t && t' == a)) wargs0) vargs0
               targs0 <- map2M (\ a f -> 
                                if f then find (\ t -> 
                                                case t of
                                                  Comb _ r -> r == a
                                                  _ -> False) wargs0
                                else return a) vargs0 nestf0
               let gvlist0 = zip wargs0 gargs0
               xargs <- mapM (\ v -> v `assoc` gvlist0) targs0
               l1' <- (fst . stripComb) `fmap` rand l1
               itm0 <- listMkAbs gargs0 =<< listMkComb l1' xargs
               let inst0 = (vc0, itm0)
                   (vc1, wargs1) = stripComb r1
               (_, vargs1) <- stripComb `fmap` rand l1
               gargs1 <- mapM (genVar . typeOf) wargs1
               targs1 <- map2M (\ a f ->
                                if f then find (\ t ->
                                                case t of
                                                  Comb _ r -> r == a
                                                  _ -> False) wargs1
                                else return a) vargs1 nestf0
               let gvlist1 = zip wargs1 gargs1
               xargs' <- mapM (\ v -> v `assoc` gvlist1) targs1
               l0' <- (fst . stripComb) `fmap` rand l0
               itm1 <- listMkAbs gargs1 =<< listMkComb l0' xargs'
               let inst1 = (vc1, itm1)
               return (inst0, inst1)

        clauseCorresponds :: HOLTerm -> HOLTerm -> HOL cls thry Bool
        clauseCorresponds cl0 cl1 =
            do (f0, ctm0) <- destComb =<< lhs cl0
               c0 <- liftM fst . destConst . fst $ stripComb ctm0
               (dty0, rty0) <- destFunTy $ typeOf f0
               (f1, ctm1) <- destComb =<< lhs cl1
               c1 <- liftM fst . destConst . fst $ stripComb ctm1
               (dty1, rty1) <- destFunTy $ typeOf f1
               return $! c0 == c1 && dty0 == rty1 && rty0 == dty1

        grabType :: HOLTerm -> HOL cls thry HOLType
        grabType = typeOf . rand . lHand . snd . stripForall

liftTypeBijections :: IndTypesCtxt thry => [HOLThm] 
                   -> HOLType 
                   -> HOL cls thry HOLThm
liftTypeBijections iths cty =
    do itys <- mapM (liftM (head . snd) . destType <=< typeOf . lHand . concl) 
                 iths
       (cty `assoc` zip itys iths <|>
        (if not $ any (flip occursIn cty) itys
            then primINST_TYPE [(tyA, cty)] thmISO_REFL
            else do (tycon, isotys) <- destType cty
                    if tycon == tyOpFun
                       then ruleMATCH_MP thmISO_FUN =<< foldr1M ruleCONJ =<<
                              mapM (liftTypeBijections iths) isotys
                    else fail $ "liftTypeBijections: Unexpected type operator "
                                ++ show tycon))


convPUSH_EXISTS :: TheoremsCtxt thry => Conversion cls thry 
                -> Conversion cls thry
convPUSH_EXISTS bc = Conv $ \ tm -> 
    runConv (convREWR thmSWAP_EXISTS `_THEN` convBINDER (convPUSH_EXISTS bc)) tm
      <|> runConv bc tm

convBREAK_CONS :: TheoremsCtxt thry => Conversion cls thry
convBREAK_CONS = Conv $ \ tm ->
    do net <- Base.basicRectypeNet
       let conv0 = convTOP_SWEEP (gconvREWRITES net)
           conv1 = if isConj tm then convLAND conv0 else conv0
       runConv (conv1 `_THEN` (convGEN_REWRITE convDEPTH 
                                 [ thmAND_CLAUSES, thmOR_CLAUSES ] `_THEN` 
                               convASSOC thmCONJ_ASSOC)) tm

convUNWIND :: IndTypesCtxt thry => Conversion cls thry
convUNWIND = Conv $ \ tm ->
    let (evs, bod) = stripExists tm
        eqs = conjuncts bod in
      (do eq <- find (\ x ->
                  case x of
                    (l := r) -> (l `elem` evs && not (l `freeIn` r)) ||
                                (r `elem` evs && not (r `freeIn` l))
                    _ -> False) eqs
          (l, r) <- destEq eq
          let v = if l `elem` evs && not (l `freeIn` r) then l else r
              cjs' = eq : (eqs \\ [eq])
              n = length evs - (1 + (try' $ index v (reverse evs)))
          th1 <- ruleCONJ_ACI =<< mkEq bod =<< listMkConj cjs'
          th2 <- foldrM ruleMK_EXISTS th1 evs
          th3 <- runConv (funpow n convBINDER (convPUSH_EXISTS baseconv)) $ 
                   rand (concl th2)
          ruleCONV (convRAND convUNWIND) $ primTRANS th2 th3) <|>
      primREFL tm
  where baseconv :: IndTypesCtxt thry => Conversion cls thry
        baseconv =
            convGEN_REWRITE id 
              [ thmUNWIND1, thmUNWIND2
              , convUNWIND_pth1, convUNWIND_pth2
              ]
        
        convUNWIND_pth1 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth1 = cacheProof "convUNWIND_pth1" ctxtIndTypes $
            ruleEQT_INTRO =<< ruleSPEC_ALL thmEXISTS_REFL

        convUNWIND_pth2 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth2 = cacheProof "convUNWIND_pth2" ctxtIndTypes $
            ruleEQT_INTRO =<< ruleGSYM (ruleSPEC_ALL thmEXISTS_REFL)

convFORALL_UNWIND :: IndTypesCtxt thry => Conversion cls thry
convFORALL_UNWIND = Conv $ \ tm ->
    let (avs, bod) = stripForall tm in
      do (ant, con) <- destImp bod
         let eqs = conjuncts ant
         eq <- findM (\ x -> 
               if isEq x then return True
               else do (xl, xr) <- destEq tm
                       return $! (xl `elem` avs && not (xl `freeIn` xr)) ||
                                 (xr `elem` avs && not (xr `freeIn` xl))) eqs
         (l, r) <- destEq eq
         let v = if l `elem` avs && not (l `freeIn` r) then l else r
             cjs' = eq : (eqs \\ [eq])
             n = length avs - (1 + (try' . index v $ reverse avs))
         th1 <- ruleCONJ_ACI =<< mkEq ant =<< listMkConj cjs'
         th2 <- ruleAP_THM (ruleAP_TERM (rand $ rator bod) th1) con
         th3 <- foldrM ruleMK_FORALL th2 avs
         th4 <- runConv (funpow n convBINDER convPUSH_FORALL) $ rand (concl th3)
         ruleCONV (convRAND convFORALL_UNWIND) $ primTRANS th3 th4
  where convPUSH_FORALL :: IndTypesCtxt thry => Conversion cls thry
        convPUSH_FORALL =
            (convREWR thmSWAP_FORALL `_THEN` convBINDER convPUSH_FORALL) 
            `_ORELSE` convGEN_REWRITE id [ convFORALL_UNWIND_pth1
                                         , convFORALL_UNWIND_pth2
                                         , convFORALL_UNWIND_pth3
                                         , convFORALL_UNWIND_pth4
                                         ]
        
        convFORALL_UNWIND_pth1 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth1 = 
          cacheProof "convFORALL_UNWIND_pth1" ctxtIndTypes $
            ruleMESON_NIL [txt| (!x. x = a /\ p x ==> q x) <=> (p a ==> q a) |]

        convFORALL_UNWIND_pth2 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth2 = 
          cacheProof "convFORALL_UNWIND_pth2"  ctxtIndTypes $
            ruleMESON_NIL [txt| (!x. a = x /\ p x ==> q x) <=> (p a ==> q a) |]

        convFORALL_UNWIND_pth3 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth3 = 
          cacheProof "convFORALL_UNWIND_pth3"  ctxtIndTypes $
            ruleMESON_NIL [txt| (!x. x = a ==> q x) <=> q a |]

        convFORALL_UNWIND_pth4 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth4 = 
          cacheProof "convFORALL_UNWIND_pth4"  ctxtIndTypes $
            ruleMESON_NIL [txt| (!x. a = x ==> q x) <=> q a |]


convMATCH_ONEPATTERN_TRIV :: IndTypesCtxt thry => Conversion cls thry
convMATCH_ONEPATTERN_TRIV =
    convMATCH_ONEPATTERN `_THEN` convGEN_REWRITE id [convUNWIND_pth5]
  where convUNWIND_pth5 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth5 = cacheProof "convUNWIND_pth5" ctxtIndTypes .
            prove [txt| (if ?!z. z = k then @z. z = k else @x. F) = k |] $
              tacMESON_NIL

convMATCH_ONEPATTERN :: IndTypesCtxt thry => Conversion cls thry
convMATCH_ONEPATTERN = Conv $ \ tm ->
    do th1 <- runConv (convGEN_REWRITE id [convUNWIND_pth3]) tm
       tm' <- body =<< rand =<< lHand =<< rand (concl th1)
       th2 <- runConv (convINSIDE_EXISTS
                       (convGEN_REWRITE id [convUNWIND_pth4] `_THEN`
                        convRAND convBREAK_CONS) `_THEN`
                       convUNWIND `_THEN`
                       convGEN_REWRITE convDEPTH
                       [ ruleEQT_INTRO =<< ruleSPEC_ALL thmEQ_REFL
                       , thmAND_CLAUSES
                       ] `_THEN`
                       convGEN_REWRITE convDEPTH [thmEXISTS_SIMP]) tm'
       let conv = Conv $ \ x -> do x' <- lHand $ concl th2
                                   if x == x' then return th2
                                   else fail ""
       ruleCONV (convRAND 
                 (convRATOR 
                  (convCOMB2 (convRAND (convBINDER conv)) 
                   (convBINDER conv)))) th1
  where convINSIDE_EXISTS :: Conversion cls thry -> Conversion cls thry
        convINSIDE_EXISTS conv = Conv $ \ tm ->
            if isExists tm 
            then runConv (convBINDER (convINSIDE_EXISTS conv)) tm
            else runConv conv tm

        convUNWIND_pth3 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth3 = cacheProof "convUNWIND_pth3" ctxtIndTypes .
            prove [txt| (_MATCH x (\y z. P y z) = 
                        if ?!z. P x z then @z. P x z else @x. F) /\ 
                        (_FUNCTION (\y z. P y z) x = 
                        if ?!z. P x z then @z. P x z else @x. F) |] $
              tacREWRITE [def_MATCH, def_FUNCTION] 

        convUNWIND_pth4 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth4 = cacheProof "convUNWIND_pth4" ctxtIndTypes $
            prove [txt| (_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> 
                         y = u /\ s = t) /\ 
                        (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> 
                         y = u /\ s = t /\ p) |] $
              tacREWRITE [ def_UNGUARDED_PATTERN, def_GUARDED_PATTERN
                         , defGEQ ] `_THEN`
              tacMESON_NIL

convMATCH_SEQPATTERN_TRIV :: IndTypesCtxt thry => Conversion cls thry
convMATCH_SEQPATTERN_TRIV = 
    convMATCH_SEQPATTERN `_THEN` convGEN_REWRITE id [thmCOND_CLAUSES]

convMATCH_SEQPATTERN :: IndTypesCtxt thry => Conversion cls thry
convMATCH_SEQPATTERN =
    convGEN_REWRITE id [convUNWIND_pth1] `_THEN`
    convRATOR (convLAND 
    (convBINDER (convRATOR convBETA `_THEN` convBETA) `_THEN`
     convPUSH_EXISTS (convGEN_REWRITE id [convUNWIND_pth2] `_THEN` 
                      convBREAK_CONS) `_THEN`
     convUNWIND `_THEN`
     convGEN_REWRITE convDEPTH [ ruleEQT_INTRO =<< ruleSPEC_ALL thmEQ_REFL
                               , thmAND_CLAUSES
                               ] `_THEN`
     convGEN_REWRITE convDEPTH [thmEXISTS_SIMP]))
  where convUNWIND_pth1 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth1 = cacheProof "convUNWIND_pth1" ctxtIndTypes .
          prove [txt| _MATCH x (_SEQPATTERN r s) =
                      (if ?y. r x y then _MATCH x r else _MATCH x s) /\
                      _FUNCTION (_SEQPATTERN r s) x =
                      (if ?y. r x y then _FUNCTION r x else _FUNCTION s x) |] $
            tacREWRITE [def_MATCH, def_SEQPATTERN, def_FUNCTION] `_THEN` 
            tacMESON_NIL

        convUNWIND_pth2 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convUNWIND_pth2 = cacheProof "convUNWIND_pth2" ctxtIndTypes $
            prove [txt| ((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> 
                         s = t) /\
                        ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> 
                         s = t /\ p) |] $
              tacREWRITE [ def_UNGUARDED_PATTERN
                         , def_GUARDED_PATTERN, defGEQ ] `_THEN`
              tacMESON_NIL
