module HaskHOL.Lib.IndTypes.Pre2 where

import HaskHOL.Core hiding (typeOf, lefts)
import HaskHOL.Core.Kernel (typeOf)
import qualified HaskHOL.Core.State as S (mkType)
import HaskHOL.Deductive

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.WF
import HaskHOL.Lib.IndTypesPre

import qualified HaskHOL.Lib.IndTypes.Pre as Pre

defineTypeRaw :: IndTypesPreCtxt thry
              => [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw def =
    do (ith, rth) <- Pre.defineTypeRaw def
       rth' <- generalizeRecursionTheorem rth
       return (ith, rth')

generalizeRecursionTheorem :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
generalizeRecursionTheorem thm =
    let (_, ebod) = stripForall $ concl thm
        (evs, bod) = stripExists ebod
        n = length evs in
      if n == 1 then return thm
      else let tys = map (\ i -> mkVarType $ "Z" `append` textShow i) 
                       [0..(n-1)] in
             do sty <- mkSum tys
                inls <- mkInls sty
                outls <- mkOutls sty
                zty <- typeOf `fmap` 
                         (rand . snd . stripForall . head $ conjuncts bod)
                ith <- primINST_TYPE [(zty, sty)] thm
                let (_, ebod') = stripForall $ concl ith
                    (evs', bod') = stripExists ebod'
                fns' <- map2M mkNewfun evs' outls
                fnalist <- zip evs' `fmap` mapM (rator <=< lhs . concl) fns'
                let inlalist = zip evs' inls
                    outlalist = zip evs' outls
                defs <- mapM (hackClause outlalist inlalist) $ conjuncts bod'
                jth <- ruleBETA $ ruleSPECL (map fst defs) ith
                bth <- primASSUME . snd . stripExists $ concl jth
                cth <- foldr1M ruleCONJ =<< mapM (finishClause outlalist) =<<
                         ruleCONJUNCTS bth
                dth <- ruleELIM_OUTCOMBS cth
                eth <- ruleGEN_REWRITE convONCE_DEPTH (map ruleSYM fns') dth
                fth <- foldrM ruleSIMPLE_EXISTS eth (map snd fnalist)
                let dtms = map (head . hyp) fns'
                gth <- foldrM (\ e th -> do (l, r) <- destEq e
                                            th' <- ruleDISCH e th
                                            th'' <- primINST [(l, r)] th'
                                            ruleMP th'' $ primREFL r) fth dtms
                hth <- rulePROVE_HYP jth $ 
                         foldrM ruleSIMPLE_CHOOSE gth evs'
                xvs <- mapM (fmap (fst . stripComb) . 
                               (rand . snd . stripForall)) . 
                         conjuncts $ concl eth
                ruleGENL xvs hth

  where ruleELIM_OUTCOMBS :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleELIM_OUTCOMBS = 
            ruleGEN_REWRITE convTOP_DEPTH 
              [getRecursiveDefinition "OUTL", getRecursiveDefinition "OUTR"]

        mkSum :: [HOLType] -> HOL cls thry HOLType
        mkSum tys =
            let k = length tys in
              if k == 1 then return $! head tys
              else do (tys1, tys2) <- trySplitAt (k `div` 2) tys
                      tys1' <- mkSum tys1
                      tys2' <- mkSum tys2
                      mkType "sum" [tys1', tys2']

        mkInls :: HOLType -> HOL cls thry [HOLTerm]
        mkInls typ =
            do bods <- mkInlsRec typ
               mapM (\ t -> mkAbs (try' $ findTerm isVar t) t) bods
          where mkInlsRec :: HOLType -> HOL cls thry [HOLTerm]
                mkInlsRec ty@TyVar{} = sequence [mkVar "x" ty]
                mkInlsRec ty =
                    do (_, [ty1, ty2]) <- destType ty
                       inls1 <- mkInlsRec ty1
                       inls2 <- mkInlsRec ty2
                       inl <- mkConst "INL" [(tyA, ty1), (tyB, ty2)]
                       inr <- mkConst "INR" [(tyA, ty1), (tyB, ty2)]
                       insl1' <- mapM (mkComb inl) inls1
                       insl2' <- mapM (mkComb inr) inls2
                       return $! insl1' ++ insl2'

        mkOutls :: HOLType -> HOL cls thry [HOLTerm]
        mkOutls typ =
            let x = mkVar "x" typ in
              do inls <- mkOutlsRec x typ
                 mapM (mkAbs x) inls
          where mkOutlsRec :: HOLTermRep tm cls thry 
                           => tm -> HOLType -> HOL cls thry [HOLTerm]
                mkOutlsRec sof TyVar{} =
                    do tm <- toHTm sof
                       return [tm]
                mkOutlsRec sof ty =
                    do (_, [ty1, ty2]) <- destType ty
                       outl <- mkConst "OUTL" [(tyA, ty1), (tyB, ty2)]
                       outr <- mkConst "OUTR" [(tyA, ty1), (tyB, ty2)]
                       outl' <- mkOutlsRec (mkComb outl sof) ty1
                       outr' <- mkOutlsRec (mkComb outr sof) ty2
                       return $! outl' ++ outr'

        mkNewfun :: HOLTerm -> HOLTerm -> HOL cls thry HOLThm
        mkNewfun fn outl =
            do (s, ty) <- destVar fn
               dty <- (head . snd) `fmap` destType ty
               let x = mkVar "x" dty
               (y, bod) <- destAbs outl
               fnx <- mkComb fn x
               r <- mkAbs x =<< varSubst [(y, fnx)] bod
               let l = mkVar s $ typeOf r
               etm <- mkEq l r
               ruleRIGHT_BETAS [x] $ primASSUME etm

        hackClause :: HOLTermEnv -> HOLTermEnv -> HOLTerm 
                   -> HOL cls thry (HOLTerm, HOLTerm)
        hackClause outlalist inlalist tm =
            let (_, bod) = stripForall tm in
              do (l, r) <- destEq bod
                 let (fn, args) = stripComb r
                 pargs <- mapM (\ a -> 
                                do g <- genVar $ typeOf a
                                   if isVar a 
                                      then return (g, g)
                                      else do outl <- flip assoc outlalist =<< 
                                                        rator a
                                              outl' <- mkComb outl g
                                              return (outl', g)) args
                 let (args', args'') = unzip pargs
                 inl <- flip assoc inlalist =<< rator l
                 rty <- (head . snd) `fmap` (destType $ typeOf inl)
                 nty <- foldrM (mkFunTy . typeOf) rty args'
                 (fname, _) <- destVar fn
                 let fn' = mkVar fname nty
                 r' <- listMkAbs args'' =<< mkComb inl =<< listMkComb fn' args'
                 return (r', fn)

        finishClause :: BoolCtxt thry => HOLTermEnv -> HOLThm 
                     -> HOL cls thry HOLThm
        finishClause outlalist t =
            let (avs, bod) = stripForall $ concl t in
              do outl <- flip assoc outlalist =<< rator (lHand bod)
                 th' <- ruleSPECL avs t
                 ruleGENL avs . ruleBETA $ ruleAP_TERM outl th'
                
proveConstructorsInjective :: PairCtxt thry => HOLThm 
                           -> HOL cls thry HOLThm
proveConstructorsInjective ax =
    let cls = conjuncts . snd . stripExists . snd . stripForall $ concl ax in
      do pats <- mapM (rand <=< lHand . snd . stripForall) cls
         foldr1M ruleCONJ =<< mapFilterM proveDistinctness pats
  where ruleDEPAIR :: PairCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleDEPAIR = ruleGEN_REWRITE convTOP_SWEEP [thmPAIR_EQ]

        proveDistinctness :: PairCtxt thry
                          => HOLTerm 
                          -> HOL cls thry HOLThm
        proveDistinctness pat =
            let (f, args) = stripComb pat in
              do rt <- foldr1M mkPair args
                 ty <- mkFunTy (typeOf pat) $ typeOf rt
                 fn <- genVar ty
                 dtm <- mkEq (mkComb fn pat) rt
                 eth <- proveRecursiveFunctionsExist ax =<<
                          listMkForall args dtm
                 let args' = variants args args
                 atm <- mkEq pat =<< listMkComb f args'
                 ath <- primASSUME atm
                 bth <- ruleAP_TERM fn ath
                 cth1 <- ruleSPECL args $ primASSUME =<< 
                           snd `fmap` (destExists $ concl eth)
                 cth2 <- primINST (zip args args') cth1
                 pth <- primTRANS (primTRANS (ruleSYM cth1) bth) cth2
                 qth <- ruleDEPAIR pth
                 let qtm = concl qth
                 qths <- ruleCONJUNCTS $ primASSUME qtm
                 fth <- primREFL f
                 rth <- foldlM primMK_COMB fth qths
                 tth <- ruleIMP_ANTISYM (ruleDISCH atm qth) $ ruleDISCH qtm rth
                 uth <- ruleGENL args $ ruleGENL args' tth
                 rulePROVE_HYP eth $ ruleSIMPLE_CHOOSE fn uth

proveDistinct_pth :: ClassicCtxt thry => HOL cls thry HOLThm
proveDistinct_pth = cacheProof "proveDistinct_pth" ctxtClassic $ 
    ruleTAUT [txt| a ==> F <=> ~a |]

proveConstructorsDistinct :: WFCtxt thry => HOLThm -> HOL cls thry HOLThm
proveConstructorsDistinct ax =
    let cls = conjuncts . snd . stripExists . snd . stripForall $ concl ax in
      do lefts <- mapM (destComb <=< lHand . snd . stripForall) cls
         let fns = foldr (insert . fst) [] lefts
             pats = map (\ f -> map snd (filter (\ (x,_) -> x == f) lefts)) fns
         foldr1M ruleCONJ =<< 
           (foldr1 (++)) `fmap` (mapFilterM proveDistinct pats)
  where allopairs :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
        allopairs _ [] _ = return []
        allopairs f (l:ls) (_:ms) =
            do xs <- mapM (f l) ms
               ys <- allopairs f ls ms
               return $! xs ++ ys
        allopairs _ _ _ = return []

        ruleNEGATE :: (ClassicCtxt thry, HOLThmRep thm cls thry) 
                   => thm -> HOL cls thry HOLThm
        ruleNEGATE = ruleGEN_ALL . ruleCONV (convREWR proveDistinct_pth)

        ruleREWRITE' :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                     => HOLTerm -> thm -> HOL cls thry HOLThm
        ruleREWRITE' bod th =
            do ths <- ruleCONJUNCTS $ primASSUME bod
               ruleGEN_REWRITE convONCE_DEPTH ths th

        proveDistinct :: WFCtxt thry => [HOLTerm] -> HOL cls thry [HOLThm]
        proveDistinct pat =
            do tyNum <- S.mkType "num" ([]::[HOLType])
               nms <- mapM mkNumeral ([0..(length pat -1)] :: [Int])
               fn <- genVar =<< mkType "fun" [typeOf $ head pat, tyNum]
               ls <- mapM (mkComb fn) pat
               defs <- map2M (\ l r -> do l' <- frees `fmap` rand l
                                          listMkForall l' =<< mkEq l r) ls nms
               eth <- proveRecursiveFunctionsExist ax =<< listMkConj defs
               (ev, bod) <- destExists $ concl eth
               pat' <-mapM (\ t -> let (f, args) = if isNumeral t
                                                   then (t, [])
                                                   else stripComb t in
                                     listMkComb f $ variants args args) pat
               pairs <- allopairs mkEq pat pat'
               nths <- mapM (ruleREWRITE' bod . ruleAP_TERM fn . primASSUME)
                         pairs
               fths <- map2M (\ t th -> ruleNEGATE . ruleDISCH t $ 
                                          ruleCONV convNUM_EQ th) pairs nths
               ruleCONJUNCTS . rulePROVE_HYP eth .
                 ruleSIMPLE_CHOOSE ev $ foldr1M ruleCONJ fths
