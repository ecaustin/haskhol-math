{-# LANGUAGE PatternSynonyms #-}
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
    , thmINJ_INVERSE2
    , thmNUMPAIR_INJ_LEMMA
    , thmNUMSUM_INJ
    , specNUMPAIR_DEST
    , specNUMSUM_DEST
    , defINJN
    , defINJA
    , defINJF
    , defINJP
    , defZCONSTR
    , defZBOT
    , rulesZRECSPACE
    , inductZRECSPACE
    , casesZRECSPACE
    , tyDefMkRecspace
    , tyDefDestRecspace
    , defBOTTOM
    , defCONSTR
    , defFCONS
    , defFNIL
    , thmINJN_INJ -- stage2
    , thmINJA_INJ
    , thmINJF_INJ
    , thmINJP_INJ
    , thmMK_REC_INJ
    , thmDEST_REC_INJ
    , thmZCONSTR_ZBOT --stage3
    , thmCONSTR_INJ
    , thmCONSTR_IND
    , thmCONSTR_BOT --stage4
    , thmCONSTR_REC --stage5
    , Pre.inductSUM
    , Pre.recursionSUM
    , Pre.defOUTL
    , Pre.defOUTR
    , inductOPTION -- stage1
    , recursionOPTION
    , inductLIST
    , recursionLIST
    , defISO
    , thmISO_REFL -- stage2
    , thmISO_FUN
    , thmISO_USAGE
    , defineType
    , getType
    , convFORALL_UNWIND
    , convMATCH_ONEPATTERN
    , convMATCH_ONEPATTERN_TRIV
    , convMATCH_SEQPATTERN
    , convMATCH_SEQPATTERN_TRIV
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)

import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypes.A
import HaskHOL.Lib.IndTypes.B
import qualified HaskHOL.Lib.IndTypes.Pre as Pre

import HaskHOL.Lib.IndTypes.Base
import HaskHOL.Lib.IndTypes.Context

import qualified Data.Text.Lazy as T (words)

defISO :: IndTypesCtxt thry => HOL cls thry HOLThm
defISO = cacheProof "defISO" ctxtIndTypes $ getDefinition "ISO"

indDefOption :: IndTypesCtxt thry => HOL cls thry (HOLThm, HOLThm)
indDefOption =
    do defs <- getIndDefs
       let (_, th1, th2) = fromJust (mapLookup "option" defs)
       return (th1, th2)

inductOPTION :: IndTypesCtxt thry => HOL cls thry HOLThm
inductOPTION = cacheProof "inductOPTION" ctxtIndTypes $
    liftM fst indDefOption

recursionOPTION :: IndTypesCtxt thry => HOL cls thry HOLThm
recursionOPTION = cacheProof "recursionOPTION" ctxtIndTypes $
    liftM snd indDefOption


indDefList :: IndTypesCtxt thry => HOL cls thry (HOLThm, HOLThm)
indDefList =
    do defs <- getIndDefs
       let (_, th1, th2) = fromJust (mapLookup "list" defs)
       return (th1, th2)

inductLIST :: IndTypesCtxt thry => HOL cls thry HOLThm
inductLIST = cacheProof "inductLIST" ctxtIndTypes $
    liftM fst indDefList

recursionLIST :: IndTypesCtxt thry => HOL cls thry HOLThm
recursionLIST = cacheProof "recursionLIST" ctxtIndTypes $
    liftM snd indDefList


thmISO_REFL :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_REFL = cacheProof "thmISO_REFL" ctxtIndTypes $
    prove [str| ISO (\x:A. x) (\x. x) |] $ tacREWRITE [defISO]

thmISO_FUN :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_FUN = cacheProof "thmISO_FUN" ctxtIndTypes .
    prove [str| ISO (f:A->A') f' /\ ISO (g:B->B') g'
                ==> ISO (\h a'. g(h(f' a'))) (\h a. g'(h(f a))) |] $
      tacREWRITE [defISO, thmFUN_EQ] `_THEN` tacMESON_NIL

thmISO_USAGE :: IndTypesCtxt thry => HOL cls thry HOLThm
thmISO_USAGE = cacheProof "thmISO_USAGE" ctxtIndTypes .
    prove [str| ISO f g
                ==> (!P. (!x. P x) <=> (!x. P(g x))) /\
                    (!P. (?x. P x) <=> (?x. P(g x))) /\
                    (!a b. (a = g b) <=> (f a = b)) |] $
      tacREWRITE [defISO, thmFUN_EQ] `_THEN` tacMESON_NIL

proveITT_pth :: IndTypesCtxt thry => HOL cls thry HOLThm
proveITT_pth = cacheProof "proveITT_pth" ctxtIndTypes .
    prove "(?) P ==> (c = (@)P) ==> P c" $
      tacGEN_REWRITE (convLAND . convRAND) [ruleGSYM axETA] `_THEN`
      tacDISCH `_THEN` _DISCH_THEN tacSUBST1 `_THEN`
      tacMATCH_MP axSELECT `_THEN` _POP_ASSUM tacACCEPT

defineType :: IndTypesCtxt thry => Text -> HOL Theory thry (HOLThm, HOLThm)
defineType s =
    do acid <- openLocalStateHOL (InductiveTypes mapEmpty)
       indTys <- queryHOL acid GetInductiveTypes
       closeAcidStateHOL acid
       let s' = head $ T.words s
       case mapLookup s' indTys of
         Just retval -> 
             return retval
         Nothing ->
             do defspec <- parseInductiveTypeSpecification s
                let newtypes = map fst defspec
                    constructors = foldr ((++) . map fst) [] $ map snd defspec
                failWhen (return $ (length (setify newtypes)) /= 
                                   length newtypes)
                  "defineType: multiple definitions of a type."
                failWhen (return $ (length (setify constructors)) /= 
                                   length constructors)
                  "defineType: multiple instances of a constructor."
                cond1 <- mapM (can getTypeArity . fromJust . destVarType) 
                           newtypes
                cond2 <- mapM (can getConstType) constructors
                if or cond1
                   then do t <- findM (can getTypeArity) . catMaybes $ 
                                  map destVarType newtypes
                           fail $ "defineType: type " ++ show t ++
                                  " already defined."
                   else if or cond2
                        then do t <- findM (can getConstType) constructors
                                fail $ "defineType: constant " ++ show t ++ 
                                       " already defined."
                        else do retval <- defineTypeRaw defspec
                                acid' <- openLocalStateHOL (InductiveTypes mapEmpty)
                                updateHOL acid' (AddInductiveType s' retval)
                                createCheckpointAndCloseHOL acid'
                                return retval

getType :: Text -> HOL cls thry (HOLThm, HOLThm)
getType name =
    do acid <- openLocalStateHOL (InductiveTypes mapEmpty)
       qth <- queryHOL acid (GetInductiveType name)
       closeAcidStateHOL acid
       liftMaybe ("getType: type " ++ show name ++ 
                  " not found.") qth


defineTypeRaw :: IndTypesCtxt thry
              => [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw def =
    let newtys = map fst def
        truecons = foldr (++) [] $ map (map fst . snd) def in
      do (p, ith0, rth0) <- defineTypeNested def
         let (avs, etm) = stripForall $ concl rth0
             allcls = conjuncts . snd $ stripExists etm
             relcls = fst . fromJust $ chopList (length truecons) allcls
             gencons = fromJust $ mapM (repeatM rator <=< rand <=< lHand .
                                        snd . stripForall) relcls
         cdefs <- map2M (\ s r -> do dth <- newDefinition s =<< 
                                              mkEq (mkVar s $ typeOf r) r
                                     liftO $ ruleSYM dth) truecons gencons
         let tavs = mkArgs "f" [] $ map typeOf avs
         ith1 <- ruleSUBS cdefs ith0
         rth1 <- ruleGENL tavs =<< ruleSUBS cdefs =<< ruleSPECL tavs rth0
         let retval = (p, ith1, rth1)
             newentries = map (\s -> (fromJust $ destVarType s, retval)) newtys
         addIndDefs newentries
         mapM_ extendRectypeNet newentries
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
                let cls = fromRight . mapM (modifyClause tyal) $ def ++ ncls
                (_, ith1, rth1) <- defineTypeNested cls
                let xnewtys = map (head . snd . fromJust . destType . typeOf) .
                                fst . stripExists . snd . stripForall $ 
                                  concl rth1
                    xtyal = fromJust . mapM 
                              (\ ty -> 
                               do s <- destVarType ty
                                  s' <- findM (\ t -> 
                                               do (t', _) <- destType t
                                                  let (op, _) = destTypeOp t'
                                                  return $! op == s) xnewtys
                                  return (ty, s')) $ map fst cls
                    ith0 = primINST_TYPE xtyal ith
                    rth0 = primINST_TYPE xtyal rth
                (isoth, rclauses) <- proveInductiveTypesIsomorphic n k 
                                       (ith0, rth0) (ith1, rth1)
                irth3 <- ruleCONJ ith1 rth1
                let vtylist = foldr (insert . typeOf) [] . variables $ 
                                concl irth3
                isoths <- ruleCONJUNCTS isoth
                let isotys = fromJust $ mapM (liftM (head . snd) . destType <=<
                                          liftM typeOf . lHand . concl) isoths
                    ctylist = filter (\ ty -> 
                                      any (\ t -> t `occursIn` ty) isotys) 
                                vtylist
                    atylist = foldr (union . stripList destFunTy) [] ctylist
                isoths' <- mapM (liftTypeBijections isoths) $
                            filter (\ ty -> any (\ t -> t `occursIn` ty) isotys)
                              atylist
                cisoths <- mapM (ruleBETA <=< liftTypeBijections isoths') 
                             ctylist
                uisoths <- mapM ruleISO_USAGE cisoths
                let visoths = fromRight $ mapM (primASSUME . concl) uisoths
                irth3' <- ruleREWRITE_FUN_EQ visoths irth3
                let irth4 = foldr rulePROVE_HYP irth3' uisoths
                isoths'' <- mapM ruleSIMPLE_ISO_EXPAND isoths'
                irth5 <- ruleREWRITE (rclauses : isoths'') irth4
                irth6 <- repeatM ruleSCRUB_ASSUMPTION irth5
                let ncjs = filter (\ t -> 
                             let ts = snd . stripComb . fromJust $ rand =<< 
                                        (lhs . snd $ stripForall t) in
                               any (\ v -> not $ isVar v) ts) . conjuncts . 
                             snd . stripExists . snd . stripForall . fromJust . 
                               rand $ concl irth6
                dths <- mapM mkNewcon ncjs
                (ith6, rth6) <- ruleCONJ_PAIR =<< rulePURE_REWRITE dths irth6
                return (n, ith6, rth6)
  where ruleSCRUB_ASSUMPTION :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleSCRUB_ASSUMPTION th =
            let hyps = hyp th 
                eqn = fromJust $ findM (\ t -> 
                        do x <- lhs t
                           return $! all (\ u -> 
                             let u' = fromJust $ rand u in
                               x `freeIn` u') hyps) hyps
                (l, r) = fromJust $ destEq eqn in
              do th' <- ruleDISCH eqn th
                 flip ruleMP (primREFL r) #<< primINST [(l, r)] th'

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
               let net' = fromJust $ foldrM (netOfThm False) net ths
               ruleCONV (convGENERAL_REWRITE True convTOP_DEPTH net' thms) thm

        defineTypeBasecase :: IndTypesCtxt thry
                           => HOL Theory thry (HOLThm, HOLThm)
        defineTypeBasecase =
            let addId _ = liftM (fst . fromJust . destVar) $ genVar tyBool in
              do def' <- mapM (return `ffCombM` (mapM (addId `ffCombM` return)))
                           def
                 Pre.defineTypeRaw def'

        mkNewcon :: PairCtxt thry => HOLTerm -> HOL Theory thry HOLThm
        mkNewcon tm =
            let (vs, bod) = stripForall tm
                rdeb = fromJust $ rand =<< lhs bod
                rdef = fromRight $ listMkAbs vs rdeb in
              do newname <- liftM (fst . fromJust . destVar) $ genVar tyBool
                 def' <- mkEq (mkVar newname $ typeOf rdef) rdef
                 dth <- newDefinition newname def'
                 ruleSIMPLE_BETA dth

        createAuxiliaryClauses :: HOLType -> 
          HOL cls thry (Int, HOLTypeEnv, 
                        [(HOLType, [(Text, [HOLType])])], HOLThm, HOLThm)
        createAuxiliaryClauses nty = 
            do id' <- liftM (fst . fromJust . destVar) $ genVar tyBool
               let (tycon, _) = fromJust $ destType nty
               indTys <- getIndDefs
               (k, ith, rth) <- liftMaybe ("definedType: Can't find definition "
                                           ++ "for nested type: " 
                                           ++ show tycon) $ 
                                  (fst $ destTypeOp tycon) `mapLookup` indTys
               let (evs, bod) = stripExists . snd . stripForall $ concl rth
                   cjs = fromJust . mapM (lHand . snd . stripForall) $ 
                           conjuncts bod
                   rtys = map (head . snd . fromJust . destType . typeOf) evs
                   tyins = fromJust $ tryFind 
                             (\ vty -> typeMatch vty nty ([], [], [])) rtys
                   cjs' = map (instFull tyins . fromJust . rand) . fst . 
                            fromJust $ chopList k cjs
                   mtys = foldr (insert . typeOf) [] cjs'
                   pcons = map (\ ty -> 
                                filter (\ t -> typeOf t == ty) cjs') mtys
                   cls' = zip mtys $ map (map (recoverClause id')) pcons
                   tyal = map (\ ty -> let x = fst . destTypeOp . fst . 
                                                 fromJust $ destType ty in
                                         (mkVarType (x `append` id'), ty)) mtys
               let cls'' = fromRight $ mapM (modifyType tyal `ffCombM` 
                                             mapM (modifyItem tyal)) cls'
               return (k, tyal, cls'', 
                       primINST_TYPE_FULL tyins ith, 
                       primINST_TYPE_FULL tyins rth)

        recoverClause :: Text -> HOLTerm -> (Text, [HOLType])
        recoverClause id' tm =
            let (con, args) = stripComb tm
                (x, _) = fromJust $ destConst con in
              (x `append` id', map typeOf args)

        modifyClause :: HOLTypeEnv -> (HOLType, [(Text, [HOLType])]) 
                     -> Either String (HOLType, [(Text, [HOLType])])
        modifyClause alist (l, lis) =
            do lis' <- mapM (modifyItem alist) lis
               return (l, lis')

        modifyItem :: HOLTypeEnv -> (Text, [HOLType]) 
                   -> Either String (Text, [HOLType])
        modifyItem alist (s, l) =
            do l' <- mapM (modifyType alist) l
               return (s, l')

        modifyType :: HOLTypeEnv -> HOLType -> Either String HOLType
        modifyType alist ty =
            case revLookup ty alist of
              Just res -> return res
              _ -> do (tycon, tyargs) <- note "modifyType" $ destType ty
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
       tmT <- liftM concl thmTRUTH
       let (pevs0, pbod0) = stripExists $ concl sth0
           (pevs1, pbod1) = stripExists $ concl sth1
           (pcjs0, _) = fromJust . chopList k $ conjuncts pbod0
           (pcjs1, _) = fromJust $ chopList k =<< 
                              (liftM snd . chopList n $ conjuncts pbod1)
           (pcjs1', pcjs0') = fromJust $ pairMapM (mapM grabType) (pcjs1, pcjs0)
           tyal0 = setify $ zip pcjs1' pcjs0'
           tyal1 = map (\ (a, b) -> (b, a)) tyal0
           tyins0 = fromRight $ mapM (\ f ->
                      do (domty, ranty) <- note "" . destFunTy $ typeOf f
                         l <- tysubst tyal0 domty
                         return (l, ranty)) pevs0
           tyins1 = fromRight $ mapM (\ f ->
                      do (domty, ranty) <- note "" . destFunTy $ typeOf f
                         l <- tysubst tyal1 domty
                         return (l, ranty)) pevs1
           tth0 = primINST_TYPE tyins0 sth0
           tth1 = primINST_TYPE tyins1 sth1
           (_, bod0) = stripExists $ concl tth0
           (_, bod1) = stripExists $ concl tth1
           (lcjs0, rcjs0) = fromJust . chopList k . map (snd . stripForall) $
                              conjuncts bod0
           (lcjs1, rcjsx) = fromJust $ chopList k =<< 
                              (liftM (map (snd . stripForall) . snd) . 
                                chopList n $ conjuncts bod1)
           rcjs1 = fromJust $ 
                     mapM (\ t -> findM (clauseCorresponds t) rcjsx) rcjs0
       (insts0, insts1) <- liftM unzip $ map2M procClause (lcjs0++rcjs0)
                                  (lcjs1++rcjs1)
       uth0 <- ruleBETA #<< primINST insts0 tth0
       uth1 <- ruleBETA #<< primINST insts1 tth1
       (efvs0, sth0') <- ruleDE_EXISTENTIALIZE uth0
       (efvs1, sth1') <- ruleDE_EXISTENTIALIZE uth1
       let efvs2 = fromJust $ mapM (\ t1 -> findM (\ t2 ->
                          do t1' <- destType $ typeOf t1
                             t2' <- destType $ typeOf t2
                             return $! (head . tail $ snd t1') == 
                                        (head $ snd t2')) efvs1) efvs0
       isotms <- map2M (\ ff gg -> listMkIComb "ISO" [ff, gg]) efvs0 efvs2
       ctm <- listMkConj isotms
       cth1 <- runConv (convISO_EXPAND) ctm
       let ctm1 = fromJust . rand $ concl cth1
           cjs = conjuncts ctm1
           eee = map (\ x -> x `mod` 2 == 0) [0..(length cjs -1)]
           (cjs1, cjs2) = partition fst $ zip eee cjs
       ctm2 <- liftM1 mkConj (listMkConj $ map snd cjs1) =<<
                 listMkConj (map snd cjs2)
       let ruleDETRIV = ruleTRIV_ANTE <=< ruleREWRITE [sth0', sth1']
       jth0 <- do itha <- ruleSPEC_ALL ith0
                  let icjs = conjuncts . fromJust . rand $ concl itha
                  cinsts <- liftO $ mapM (\ tm -> tryFind (\ vtm ->
                                   termMatch [] vtm tm) icjs) =<< 
                                     liftM conjuncts (rand ctm2)
                  let tvs = (fst . stripForall $ concl ith0) \\
                                 (foldr (\ (_, x, _) -> union (map snd x)) [] 
                                    cinsts)
                      ctvs = fromRight $ mapM (\ p ->
                                    do (_, tys) <- note "" . destType $ typeOf p
                                       let x = mkVar "x" $ head tys
                                       x' <- mkAbs x tmT
                                       return (x', p)) tvs
                  ithas <- foldrM ruleINSTANTIATE itha cinsts
                  ruleDETRIV #<< primINST ctvs ithas
       jth1 <- do itha <- ruleSPEC_ALL ith1
                  let icjs = conjuncts . fromJust . rand $ concl itha
                  cinsts <-liftO $ mapM (\ tm -> tryFind (\ vtm ->
                                   termMatch [] vtm tm) icjs) =<< 
                                     liftM conjuncts (lHand ctm2)
                  let tvs = (fst . stripForall $ concl ith1) \\
                                 (foldr (\ (_, x, _) -> union (map snd x)) []
                                    cinsts)
                      ctvs = fromRight $ mapM (\ p ->
                                    do (_, tys) <- note "" . destType $ typeOf p
                                       let x = mkVar "x" $ head tys
                                       x' <- mkAbs x tmT
                                       return (x', p)) tvs
                  ithas <- foldrM ruleINSTANTIATE itha cinsts
                  ruleDETRIV #<< primINST ctvs ithas
       cths4 <- liftM1 (map2M ruleCONJ) (ruleCONJUNCTS jth0) =<<
                       ruleCONJUNCTS jth1
       cths5 <- mapM (rulePURE_ONCE_REWRITE [ruleGSYM defISO]) cths4
       cth6 <- foldr1M ruleCONJ cths5
       cth7 <- ruleCONJ sth0' sth1'
       return (cth6, cth7)
  where ruleTRIV_ANTE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleTRIV_ANTE th =
            let tm = concl th in
              if isImp tm
              then let (ant, _) = fromJust . destImp $ concl th
                       cjs = conjuncts ant in
                     do cths <- mapM (runConv convTRIV_IMP) cjs
                        ruleMP th =<< foldr1M ruleCONJ cths
              else return th
          where convTRIV_IMP :: BoolCtxt thry => Conversion cls thry
                convTRIV_IMP = Conv $ \ tm ->
                    let (avs, bod) = stripForall tm in
                      do bth <- 
                             if isEq bod 
                             then return . primREFL . fromJust $ rand bod
                             else let (ant, con) = fromJust $ destImp bod in
                                    do ants <- ruleCONJUNCTS #<< primASSUME ant
                                       ith <- runConv (convSUBS ants) #<< 
                                                lhs con
                                       ruleDISCH ant ith
                         ruleGENL avs bth
   
        convISO_EXPAND :: IndTypesCtxt thry => Conversion cls thry
        convISO_EXPAND = convPURE_ONCE_REWRITE [defISO]

        ruleDE_EXISTENTIALIZE :: IndTypesCtxt thry => HOLThm 
                              -> HOL cls thry ([HOLTerm], HOLThm)
        ruleDE_EXISTENTIALIZE th =
            if not . isExists $ concl th then return ([], th)
            else do th1 <- ruleMATCH_MP proveITT_pth th
                    let v1 = fromJust $ rand =<< rand (concl th1)
                    gv <- genVar $ typeOf v1
                    th2 <- ruleCONV convBETA =<< ruleUNDISCH #<< 
                             primINST [(v1, gv)] th1
                    (vs, th3) <- ruleDE_EXISTENTIALIZE th2
                    return (gv:vs, th3)

        procClause :: HOLTerm -> HOLTerm 
                   -> HOL cls thry ((HOLTerm, HOLTerm), (HOLTerm, HOLTerm))
        procClause tm0 tm1 =
            let (l0, r0) = fromJust $ destEq tm0
                (l1, r1) = fromJust $ destEq tm1
                (vc0, wargs0) = stripComb r0
                (_, vargs0) = stripComb . fromJust $ rand l0 in
              do gargs0 <- mapM (genVar . typeOf) wargs0
                 let nestf0 = fromJust $ mapM (\ a -> can (findM (\ t -> 
                               do t' <- rand t
                                  return $! isComb t && t' == a)) wargs0) vargs0
                     targs0 = fromJust $ map2M (\ a f -> 
                                if f then find (\ t -> isComb t && 
                                                       rand t == Just a) wargs0
                                else Just a) vargs0 nestf0
                     gvlist0 = zip wargs0 gargs0
                     xargs = fromJust $ mapM (\ v -> v `lookup` gvlist0) targs0
                     l1' = fst . stripComb . fromJust $ rand l1
                     itm0 = fromRight $ listMkAbs gargs0 =<< 
                              listMkComb l1' xargs
                     inst0 = (vc0, itm0)
                     (vc1, wargs1) = stripComb r1
                     (_, vargs1) = stripComb . fromJust $ rand l1
                 gargs1 <- mapM (genVar . typeOf) wargs1
                 let targs1 = fromJust $ map2M (\ a f ->
                                if f then find (\ t -> isComb t &&
                                                       rand t == Just a) wargs1
                                else Just a) vargs1 nestf0
                     gvlist1 = zip wargs1 gargs1
                     xargs' = fromJust $ mapM (\ v -> v `lookup` gvlist1) targs1
                     l0' = fst . stripComb . fromJust $ rand l0
                     itm1 = fromRight $ listMkAbs gargs1 =<<
                              listMkComb l0' xargs'
                     inst1 = (vc1, itm1)
                 return (inst0, inst1)

        clauseCorresponds :: HOLTerm -> HOLTerm -> Maybe Bool
        clauseCorresponds cl0 cl1 =
            do (f0, ctm0) <- destComb =<< lhs cl0
               c0 <- liftM fst . destConst . fst $ stripComb ctm0
               (dty0, rty0) <- destFunTy $ typeOf f0
               (f1, ctm1) <- destComb =<< lhs cl1
               c1 <- liftM fst . destConst . fst $ stripComb ctm1
               (dty1, rty1) <- destFunTy $ typeOf f1
               return $! c0 == c1 && dty0 == rty1 && rty0 == dty1

        grabType :: HOLTerm -> Maybe HOLType
        grabType = liftM typeOf . rand <=< lHand . snd . stripForall

liftTypeBijections :: IndTypesCtxt thry => [HOLThm] 
                   -> HOLType 
                   -> HOL cls thry HOLThm
liftTypeBijections iths cty =
    let itys = fromJust $ mapM (liftM (head . snd) . destType <=< 
                                liftM typeOf . lHand . concl) iths in
      case cty `lookup` zip itys iths of
        Just res -> return res
        _ -> if not $ any (flip occursIn cty) itys
             then liftM (primINST_TYPE [(tyA, cty)]) thmISO_REFL
             else let (tycon, isotys) = fromJust $ destType cty in
                    if tycon == tyOpFun
                    then ruleMATCH_MP thmISO_FUN =<< foldr1M ruleCONJ =<<
                           mapM (liftTypeBijections iths) isotys
                    else fail $ "liftTypeBijections: Unexpected type operator "
                                ++ show tycon


convFORALL_UNWIND :: IndTypesCtxt thry => Conversion cls thry
convFORALL_UNWIND = Conv $ \ tm ->
    let (avs, bod) = stripForall tm
        (ant, con) = fromJust $ destImp bod
        eqs = conjuncts ant
        eq = fromJust $ findM (\ x -> 
               if isEq x then return True
               else do (xl, xr) <- destEq tm
                       return $! (xl `elem` avs && not (xl `freeIn` xr)) ||
                                 (xr `elem` avs && not (xr `freeIn` xl))) eqs
        (l, r) = fromJust $ destEq eq
        v = if l `elem` avs && not (l `freeIn` r) then l else r
        cjs' = eq : (eqs \\ [eq])
        n = length avs - (1 + (fromJust . index v $ reverse avs)) in
      do th1 <- ruleCONJ_ACI =<< mkEq ant =<< listMkConj cjs'
         let th2 = fromRight $ 
                     liftM1 ruleAP_THM (flip ruleAP_TERM th1 #<< rand =<<
                                          rator bod) con
         th3 <- foldrM ruleMK_FORALL th2 avs
         th4 <- runConv (funpow n convBINDER convPUSH_FORALL) #<<
                  rand (concl th3)
         ruleCONV (convRAND convFORALL_UNWIND) #<< primTRANS th3 th4
  where convPUSH_FORALL :: IndTypesCtxt thry => Conversion cls thry
        convPUSH_FORALL =
            (convREWR thmSWAP_FORALL `_THEN` convBINDER convPUSH_FORALL) 
            `_ORELSE` convGEN_REWRITE id [ convFORALL_UNWIND_pth1
                                         , convFORALL_UNWIND_pth2
                                         , convFORALL_UNWIND_pth3
                                         , convFORALL_UNWIND_pth4
                                         ]
        
        convFORALL_UNWIND_pth1 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth1 = cacheProof "convFORALL_UNWIND_pth1" ctxtIndTypes $
            ruleMESON_NIL [str| (!x. x = a /\ p x ==> q x) <=> (p a ==> q a) |]

        convFORALL_UNWIND_pth2 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth2 = cacheProof "convFORALL_UNWIND_pth2"  ctxtIndTypes $
            ruleMESON_NIL [str| (!x. a = x /\ p x ==> q x) <=> (p a ==> q a) |]

        convFORALL_UNWIND_pth3 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth3 = cacheProof "convFORALL_UNWIND_pth3"  ctxtIndTypes $
            ruleMESON_NIL [str| (!x. x = a ==> q x) <=> q a |]

        convFORALL_UNWIND_pth4 :: IndTypesCtxt thry => HOL cls thry HOLThm
        convFORALL_UNWIND_pth4 = cacheProof "convFORALL_UNWIND_pth4"  ctxtIndTypes $
            ruleMESON_NIL [str| (!x. a = x ==> q x) <=> q a |]
