{-# LANGUAGE PatternSynonyms #-}
module HaskHOL.Lib.IndTypes.Pre where

import HaskHOL.Core hiding (lefts)
import HaskHOL.Deductive

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.CalcNum

import HaskHOL.Lib.IndTypes.B
import qualified HaskHOL.Lib.IndTypes.B.Pre as Pre

defOUTL :: IndTypesBCtxt thry => HOL cls thry HOLThm
defOUTL = cacheProof "defOUTL" ctxtIndTypesB $ getRecursiveDefinition "OUTL"

defOUTR :: IndTypesBCtxt thry => HOL cls thry HOLThm
defOUTR = cacheProof "defOUTR" ctxtIndTypesB $ getRecursiveDefinition "OUTR"

indDefSum :: (BasicConvs thry, IndTypesBCtxt thry) 
          => HOL cls thry (HOLThm, HOLThm)
indDefSum =
    do defs <- getIndDefs
       let (_, th1, th2) = fromJust (mapLookup "sum" defs)
       return (th1, th2)

inductSUM :: (BasicConvs thry, IndTypesBCtxt thry) => HOL cls thry HOLThm
inductSUM = cacheProof "inductSUM" ctxtIndTypesB $
    liftM fst indDefSum

recursionSUM :: (BasicConvs thry, IndTypesBCtxt thry) => HOL cls thry HOLThm
recursionSUM = cacheProof "recursionSUM" ctxtIndTypesB $
    liftM snd indDefSum

defineTypeRaw :: (BasicConvs thry, IndTypesBCtxt thry) 
              => [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw def =
    do (ith, rth) <- Pre.defineTypeRaw def
       rth' <- generalizeRecursionTheorem rth
       return (ith, rth')

generalizeRecursionTheorem :: IndTypesBCtxt thry => HOLThm 
                           -> HOL cls thry HOLThm
generalizeRecursionTheorem thm =
    let (_, ebod) = stripForall $ concl thm
        (evs, _) = stripExists ebod
        n = length evs in
      if n == 1 then return thm
      else let tys = map (\ i -> mkVarType $ "Z" `append` textShow i) 
                       [0..(n-1)] in
             do sty <- mkSum tys
                inls <- mkInls sty
                outls <- mkOutls sty
                let zty = typeOf . fromJust . rand . snd . stripForall . head $
                            conjuncts bod
                    ith = primINST_TYPE [(zty, sty)] thm
                    (_, ebod') = stripForall $ concl ith
                    (evs', bod) = stripExists ebod'
                fns' <- map2M mkNewfun evs' outls
                let fnalist = zip evs' . fromJust $ 
                                mapM (rator <=< lhs . concl) fns'
                    inlalist = zip evs' inls
                    outlalist = zip evs' outls
                defs <- mapM (hackClause outlalist inlalist) $ conjuncts bod
                jth <- ruleBETA =<< ruleSPECL (map fst defs) ith
                let bth = fromRight . primASSUME . snd . stripExists $ concl jth
                cth <- foldr1M ruleCONJ =<< mapM (finishClause outlalist) =<<
                         ruleCONJUNCTS bth
                dth <- ruleELIM_OUTCOMBS cth
                eth <- ruleGEN_REWRITE convONCE_DEPTH (map ruleSYM fns') dth
                fth <- foldrM ruleSIMPLE_EXISTS eth (map snd fnalist)
                let dtms = map (head . hyp) fns'
                gth <- foldrM (\ e th -> let (l, r) = fromJust $ destEq e in
                                           do th' <- ruleDISCH e th
                                              let th'' = fromJust $ 
                                                           primINST [(l, r)] th'
                                              ruleMP th'' $ primREFL r) fth dtms
                hth <- liftM (rulePROVE_HYP jth) $ 
                         foldrM ruleSIMPLE_CHOOSE gth evs'
                let xvs = map (fst . stripComb . fromJust . rand . snd .
                               stripForall) . conjuncts $ concl eth
                ruleGENL xvs hth

  where ruleELIM_OUTCOMBS :: IndTypesBCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleELIM_OUTCOMBS = ruleGEN_REWRITE convTOP_DEPTH [defOUTL, defOUTR]

        mkSum :: [HOLType] -> HOL cls thry HOLType
        mkSum tys =
            let k = length tys in
              if k == 1 then return $! head tys
              else let (tys1, tys2) = fromJust $ chopList (k `div` 2) tys in
                     do tys1' <- mkSum tys1
                        tys2' <- mkSum tys2
                        mkType "sum" [tys1', tys2']

        mkInls :: HOLType -> HOL cls thry [HOLTerm]
        mkInls typ =
            do bods <- mkInlsRec typ
               liftO $ mapM (\ t -> flip mkAbs t #<< findTerm isVar t) bods
          where mkInlsRec :: HOLType -> HOL cls thry [HOLTerm]
                mkInlsRec ty@TyVar{} = return [mkVar "x" ty]
                mkInlsRec ty =
                    let (_, [ty1, ty2]) = fromJust $ destType ty in
                      do inls1 <- mkInlsRec ty1
                         inls2 <- mkInlsRec ty2
                         inl <- mkConst "INL" [(tyA, ty1), (tyB, ty2)]
                         inr <- mkConst "INR" [(tyA, ty1), (tyB, ty2)]
                         let insl1' = fromRight $ mapM (mkComb inl) inls1
                             insl2' = fromRight $ mapM (mkComb inr) inls2
                         return $! insl1' ++ insl2'

        mkOutls :: HOLType -> HOL cls thry [HOLTerm]
        mkOutls typ =
            let x = mkVar "x" typ in
              do inls <- mkOutlsRec x typ
                 liftO $ mapM (mkAbs x) inls
          where mkOutlsRec :: HOLTerm -> HOLType -> HOL cls thry [HOLTerm]
                mkOutlsRec sof TyVar{} = return [sof]
                mkOutlsRec sof ty =
                    let (_, [ty1, ty2]) = fromJust $ destType ty in
                      do outl <- mkConst "OUTL" [(tyA, ty1), (tyB, ty2)]
                         outr <- mkConst "OUTR" [(tyA, ty1), (tyB, ty2)]
                         outl' <- flip mkOutlsRec ty1 #<< mkComb outl sof
                         outr' <- flip mkOutlsRec ty2 #<< mkComb outr sof
                         return $! outl' ++ outr'

        mkNewfun :: HOLTerm -> HOLTerm -> HOL cls thry HOLThm
        mkNewfun fn outl =
            let (x, l, r) = fromJust $
                             do (s, ty) <- destVar fn
                                dty <- liftM (head . snd) $ destType ty
                                let x' = mkVar "x" dty
                                (y, bod) <- destAbs outl
                                fnx <- hush $ mkComb fn x'
                                r' <- hush $ mkAbs x #<< varSubst [(y, fnx)] bod
                                let l' = mkVar s $ typeOf r'
                                return (x', l', r') in
              do etm <- mkEq l r
                 ruleRIGHT_BETAS [x] #<< primASSUME etm

        hackClause :: HOLTermEnv -> HOLTermEnv -> HOLTerm 
                   -> HOL cls thry (HOLTerm, HOLTerm)
        hackClause outlalist inlalist tm =
            let (_, bod) = stripForall tm
                (l, r) = fromJust $ destEq bod
                (fn, args) = stripComb r in
              do pargs <- mapM (\ a -> 
                                do g <- genVar $ typeOf a
                                   if isVar a 
                                      then return (g, g)
                                      else let outl = fromJust $ flip lookup
                                                        outlalist =<< rator a
                                               outl' = fromRight $ 
                                                         mkComb outl g in
                                             return (outl', g)) args
                 let (args', args'') = unzip pargs
                     inl = fromJust $ flip lookup inlalist =<< rator l
                     rty = head . snd . fromJust . destType $ typeOf inl
                 nty <- foldrM (mkFunTy . typeOf) rty args'
                 let fn' = mkVar (fst . fromJust $ destVar fn) nty
                     r' = fromRight $ listMkAbs args'' =<< mkComb inl =<<
                            listMkComb fn' args'
                 return (r', fn)

        finishClause :: BoolCtxt thry => HOLTermEnv -> HOLThm 
                     -> HOL cls thry HOLThm
        finishClause outlalist t =
            let (avs, bod) = stripForall $ concl t
                outl = fromJust $ flip lookup outlalist =<< rator =<< 
                         lHand bod in
              do th' <- ruleSPECL avs t
                 ruleGENL avs =<< ruleBETA #<< ruleAP_TERM outl th'
                
proveConstructorsInjective :: (BasicConvs thry, PairCtxt thry) => HOLThm 
                           -> HOL cls thry HOLThm
proveConstructorsInjective ax =
    let cls = conjuncts . snd . stripExists . snd . stripForall $ concl ax
        pats = fromJust $ mapM (rand <=< lHand . snd . stripForall) cls in
      foldr1M ruleCONJ =<< mapFilterM proveDistinctness pats
  where ruleDEPAIR :: (BasicConvs thry, PairCtxt thry) => HOLThm 
                   -> HOL cls thry HOLThm
        ruleDEPAIR = ruleGEN_REWRITE convTOP_SWEEP [thmPAIR_EQ]

        proveDistinctness :: (BasicConvs thry, PairCtxt thry)
                          => HOLTerm 
                          -> HOL cls thry HOLThm
        proveDistinctness pat =
            let (f, args) = stripComb pat in
              do rt <- foldr1M mkPair args
                 ty <- mkFunTy (typeOf pat) $ typeOf rt
                 fn <- genVar ty
                 dtm <- flip mkEq rt #<< mkComb fn pat
                 eth <- proveRecursiveFunctionsExist ax =<< 
                          listMkForall args dtm
                 let args' = variants args args
                 atm <- mkEq pat #<< listMkComb f args'
                 let ath = fromRight $ primASSUME atm
                     bth = fromRight $ ruleAP_TERM fn ath
                 cth1 <- ruleSPECL args #<< primASSUME #<< 
                           liftM snd (destExists $ concl eth)
                 let cth2 = fromJust $ primINST (zip args' args) cth1
                     pth = fromRight $ liftM1 primTRANS 
                             (liftM1 primTRANS (ruleSYM cth1) bth) cth2
                 qth <- ruleDEPAIR pth
                 let qtm = concl qth
                 qths <- ruleCONJUNCTS #<< primASSUME qtm
                 let rth = fromRight $ foldlM (flip primMK_COMB) (primREFL f) 
                             qths
                 tth <- liftM1 ruleIMP_ANTISYM (ruleDISCH atm qth) =<< 
                          ruleDISCH qtm rth
                 uth <- ruleGENL args =<< ruleGENL args' tth
                 liftM (rulePROVE_HYP eth) $ ruleSIMPLE_CHOOSE fn uth

proveDistinct_pth :: (BasicConvs thry, IndTypesBCtxt thry) 
                  => HOL cls thry HOLThm
proveDistinct_pth = cacheProof "proveDistinct_pth" ctxtIndTypesB $ 
    ruleTAUT "a ==> F <=> ~a"

proveConstructorsDistinct :: (BasicConvs thry, IndTypesBCtxt thry) => HOLThm 
                          -> HOL cls thry HOLThm
proveConstructorsDistinct ax =
    let cls = conjuncts . snd . stripExists . snd . stripForall $ concl ax
        lefts = fromJust $ mapM (destComb <=< lHand . snd . stripForall) cls
        fns = foldr (insert . fst) [] lefts
        pats = map (\ f -> map snd (filter (\ (x,_) -> x == f) lefts)) fns in
      foldr1M ruleCONJ =<< liftM (foldr1 (++))
        (mapFilterM proveDistinct pats)
  where allopairs :: Monad m => (a -> a -> m a) -> [a] -> [a] -> m [a]
        allopairs _ [] _ = return []
        allopairs f (l:ls) (_:ms) =
            do xs <- mapM (f l) ms
               ys <- allopairs f ls ms
               return $! xs ++ ys
        allopairs _ _ _ = return []

        ruleNEGATE :: (BasicConvs thry, IndTypesBCtxt thry) => HOLThm 
                   -> HOL cls thry HOLThm
        ruleNEGATE = ruleGEN_ALL <=< ruleCONV (convREWR proveDistinct_pth)

        ruleREWRITE' :: BoolCtxt thry => HOLTerm -> HOLThm 
                     -> HOL cls thry HOLThm
        ruleREWRITE' bod th =
            do ths <- ruleCONJUNCTS #<< primASSUME bod
               ruleGEN_REWRITE convONCE_DEPTH ths th

        proveDistinct :: (BasicConvs thry, IndTypesBCtxt thry) 
                      => [HOLTerm] -> HOL cls thry [HOLThm]
        proveDistinct pat =
            do tyNum <- mkType "num" []
               nums <- mapM mkNumeral ([0..(length pat -1)] :: [Int])
               fn <- genVar =<< mkType "fun" [typeOf $ head pat, tyNum]
               let ls = fromRight $ mapM (mkComb fn) pat
               defs <- map2M (\ l r -> let l' = frees . fromJust $ rand l in
                                         listMkForall l' =<< mkEq l r) ls nums
               eth <- proveRecursiveFunctionsExist ax =<< listMkConj defs
               let (ev, bod) = fromJust . destExists $ concl eth
                   pat' = fromRight $ mapM (\ t ->
                                            let (f, args) = if isNumeral t
                                                            then (t, [])
                                                            else stripComb t in
                                              listMkComb f $ variants args args)
                            pat
               pairs <- allopairs mkEq pat pat'
               nths <- mapM (ruleREWRITE' bod <#< ruleAP_TERM fn <=< primASSUME)
                         pairs
               fths <- map2M (\ t th -> ruleNEGATE =<< ruleDISCH t =<< 
                                          ruleCONV convNUM_EQ th) pairs nths
               ruleCONJUNCTS =<< liftM (rulePROVE_HYP eth) 
                 (ruleSIMPLE_CHOOSE ev =<< foldr1M ruleCONJ fths)
