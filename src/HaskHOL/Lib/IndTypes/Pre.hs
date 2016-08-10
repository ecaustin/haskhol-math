{-# LANGUAGE FlexibleContexts #-}
module HaskHOL.Lib.IndTypes.Pre where

import HaskHOL.Core hiding (typeOf)
import HaskHOL.Core.Kernel (typeOf)
import qualified HaskHOL.Core.State as S (mkType)
import HaskHOL.Deductive hiding (getDefinition, getSpecification, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.WF
import HaskHOL.Lib.IndTypesPre

tmZERO, tmSUC :: WFCtxt thry => HOL cls thry HOLTerm
tmZERO = serve [wf| 0 |]
tmSUC = serve [wf| SUC |]

sucivate :: WFCtxt thry => Int -> HOL cls thry HOLTerm
sucivate n = funpowM n (mkComb tmSUC) =<< toHTm tmZERO

ruleSCRUB_EQUATION :: BoolCtxt thry => HOLTerm -> (HOLThm, HOLTermEnv) 
                   -> HOL cls thry (HOLThm, HOLTermEnv)
ruleSCRUB_EQUATION eq (th, insts) =
    do eq' <- foldrM subst eq (map (: []) insts)
       (l, r) <- destEq eq'
       th' <- ruleDISCH eq' th
       th'' <- ruleMP (primINST [(l, r)] th') $ primREFL r
       return (th'', (l, r):insts)


justifyInductiveTypeModel :: WFCtxt thry
                          => [(HOLType, [(Text, [HOLType])])] 
                          -> HOL cls thry ([HOLThm], HOLThm, HOLThm)
justifyInductiveTypeModel def =
    do tTm <- serve [wf| T |]
       nTm <- serve [wf| n:num |]
       bepsTm <- serve [wf| @x:bool. T |]
       let (newtys, rights) = unzip def
           tyargls = foldr ((++) . map snd) [] rights
           alltys = foldr (munion . flip (\\) newtys) [] tyargls
       epstms <- mapM (\ ty -> mkSelect (mkVar "v" ty) tTm) alltys
       pty <- foldr1M (\ ty1 ty2 -> mkType "prod" [ty1, ty2]) alltys <|> 
                return tyBool
       recty <- mkType "recspace" [pty]
       constr <- mkConst "CONSTR" [(tyA, pty)]
       fcons <- mkConst "FCONS" [(tyA, recty)]
       bot <- mkConst "BOTTOM" [(tyA, pty)]
       bottail <- mkAbs nTm bot
       --
       let mkConstructor :: WFCtxt thry 
                         => Int -> (Text, [HOLType]) -> HOL cls thry HOLTerm
           mkConstructor n (cname, cargs) =
            let ttys = map (\ ty -> if ty `elem` newtys 
                                    then recty else ty) cargs
                args = mkArgs "a" [] ttys
                (rargs, iargs) = partition (\ t -> typeOf t == recty) args
                --
                mkInjector :: MonadCatch m => [HOLTerm] -> [HOLType] 
                           -> [HOLTerm] -> m [HOLTerm]
                mkInjector _ [] _ = return []
                mkInjector (tm:tms) (ty:tys) is =
                    (do (a, iargs') <- remove (\ t -> typeOf t == ty) is
                        tl <- mkInjector tms tys iargs'
                        return (a:tl))
                    <|> (do tl <- mkInjector tms tys is
                            return (tm:tl))
                mkInjector _ _ _ = fail' "mkInjector" in
                --
              do iarg <- (foldr1M mkPair =<< mkInjector epstms alltys iargs) <|>
                           return bepsTm
                 rarg <- foldrM (mkBinop fcons) bottail rargs
                 conty <- foldrM mkFunTy recty $ map typeOf args
                 n' <- sucivate n
                 condef <- listMkComb constr [n', iarg, rarg]
                 mkEq (mkVar cname conty) =<< listMkAbs args condef
       --         
           mkConstructors :: WFCtxt thry => Int -> [(Text, [HOLType])] 
                          -> HOL cls thry [HOLTerm]
           mkConstructors _ [] = return []
           mkConstructors n (x:xs) =
            do hd <- mkConstructor n x
               tl <- mkConstructors (n + 1) xs
               return (hd:tl)
       --
       condefs <- mkConstructors 0 $ concat rights
       conths <- mapM primASSUME condefs
       predty <- mkFunTy recty tyBool
       let edefs = foldr (\ (x, l) acc -> map (\ t -> (x, t)) l ++ acc) [] def
       idefs <- map2 (\ (r, (_, atys)) d -> ((r, atys), d)) edefs condefs
       --  
       let mkRule :: ((HOLType, [HOLType]), HOLTerm) 
                  -> HOL cls thry HOLTerm
           mkRule ((r, a), condef) =
             do (left, right) <- destEq condef
                let (args, _) = stripAbs right
                lapp <- listMkComb left args
                conds <- foldr2M (\ arg argty sofar ->
                           if argty `elem` newtys
                           then do ty' <- destVarType argty 
                                   arg' <- mkComb (mkVar ty' predty) arg
                                   return (arg':sofar)
                           else return sofar) [] args a
                ty' <- destVarType r
                conc <- mkComb (mkVar ty' predty) lapp
                rule <- if null conds then return conc
                        else flip mkImp conc =<< listMkConj conds
                listMkForall args rule
       --
       rules <- listMkConj =<< mapM mkRule idefs
       th0 <- deriveNonschematicInductiveRelations rules
       th1 <- proveMonotonicityHyps th0
       (th2a, th2bc) <- ruleCONJ_PAIR th1
       th2b <- ruleCONJUNCT1 th2bc
       return (conths, th2a, th2b)
  where munion :: Eq a => [a] -> [a] -> [a]
        munion s1 = try' . munion' s1
        
        munion' :: (Eq a, MonadCatch m) => [a] -> [a] -> m [a]
        munion' [] s2 = return s2
        munion' (h1:s1') s2 =
            (do (_, s2') <- remove (== h1) s2
                tl <- munion' s1' s2'
                return (h1:tl))
            <|> do tl <- munion' s1' s2
                   return (h1:tl)

proveModelInhabitation :: BoolCtxt thry => HOLThm -> HOL cls thry [HOLThm]
proveModelInhabitation rth =
    do srules <- mapM ruleSPEC_ALL =<< ruleCONJUNCTS rth
       let (imps, bases) = partition (isImp . concl) srules
       impConcs <- mapM (rand . concl) imps
       let concs = map concl bases ++ impConcs
       preds <- liftM setify $ mapM (repeatM rator) concs
       ithms <- exhaustInhabitations imps bases
       mapM (\ p -> find (\ th -> (fst . stripComb $ concl th) == p) ithms) 
         preds
           
  where exhaustInhabitations :: BoolCtxt thry => [HOLThm] -> [HOLThm] 
                             -> HOL cls thry [HOLThm]
        exhaustInhabitations ths sofar =
            let dunnit = setify $ map (fst . stripComb . concl) sofar in
              do useful <- filterM (\ (Thm _ c) -> 
                                     do c' <- (fst . stripComb) `fmap` rand c
                                        return $! c' `notElem` dunnit) ths
                 if null useful then return sofar
                 else do newth <- tryFind followHorn useful
                         exhaustInhabitations ths (newth:sofar)
          where followHorn :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
                followHorn thm =
                    do preds <- liftM (map (fst . stripComb) . conjuncts) .
                                  lHand $ concl thm
                       asms <- mapM (\ p -> 
                                 find (\ (Thm _ c') ->  fst (stripComb c') == p)
                                   sofar) preds
                       ruleMATCH_MP thm $ foldr1M ruleCONJ asms

defineInductiveType :: BoolCtxt thry => [HOLThm] -> HOLThm 
                    -> HOL Theory thry (HOLThm, HOLThm)
defineInductiveType cdefs exth@(Thm asl extm) =
    let (epred@(Var ename _), _) = stripComb extm in
      do th1@(Thm _ c1) <- primASSUME =<< 
                             findM (\ eq -> do eq' <- lHand eq
                                               return $! eq' == epred) asl
         th1' <- runConv (convSUBS cdefs) =<< rand c1
         th2 <- primTRANS th1 th1'
         th2' <- ruleAP_THM th2 =<< rand extm
         th3@(Thm asl3 _) <- primEQ_MP th2' exth
         (th4, _) <- foldrM ruleSCRUB_EQUATION (th3, []) asl3
         let mkname = "_mk_" `append` ename
             destname = "_dest_" `append` ename
         (bij1, bij2@(Thm _ bc)) <- newBasicTypeDefinition ename mkname destname
                                     th4
         bij2a <- ruleAP_THM th2 =<< rand =<< rand bc
         bij2b <- primTRANS bij2a bij2
         return (bij1, bij2b)
defineInductiveType _ _ = error "defineInductiveType: exhaustive warning."

defineInductiveTypeConstructor :: PairCtxt thry => [HOLThm] 
                               -> [(HOLTerm, (HOLTerm, HOLTerm))] 
                               -> HOLThm -> HOL Theory thry HOLThm
defineInductiveTypeConstructor defs consindex (Thm _ c) =
    let (_, bod) = stripForall c in
      do asms <- if isImp bod then liftM conjuncts $ lHand bod else return []
         conc <- if isImp bod then rand bod else return bod
         asmlist <- mapM destComb asms
         (cpred, cterm) <- destComb conc
         let (oldcon, oldargs) = stripComb cterm
         (newrights, newargs) <- mapAndUnzipM (modifyArg asmlist) oldargs
         (retmk, _) <- cpred `assoc` consindex
         defbod <- mkComb retmk =<< listMkComb oldcon newrights
         defrt <- listMkAbs newargs defbod
         expth <- findM (\ (Thm _ c') -> do c'' <- lHand c' 
                                            return $! c'' == oldcon) defs
         deflf@(Var name _) <- (\ (x, _) -> mkVar x $ typeOf defrt) =<< 
                                 destVar oldcon
         rexpth <- runConv (convSUBS [expth]) defrt
         deftm <- mkEq deflf =<< rand (concl rexpth)
         defth <- newDefinition (name, deftm)
         primTRANS defth =<< ruleSYM rexpth
  where modifyArg :: HOLTermEnv -> HOLTerm -> HOL cls thry (HOLTerm, HOLTerm)
        modifyArg asmlist v =
            (do (_, dest) <- flip assoc consindex =<< v `revAssoc` asmlist
                ty' <- liftM (head . snd) . destType $ typeOf dest
                v' <- (\ (x, _) -> mkVar x ty') =<< destVar v
                v'' <- mkComb dest v'
                return (v'', v'))
            <|> return (v, v)
defineInductiveTypeConstructor _ _ _ = 
    error "defineInductiveTypeConstructor: exhaustive warning."

instantiateInductionTheorem :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                            -> HOLThm -> HOL cls thry HOLThm
instantiateInductionTheorem consindex ith =
    let (avs, bod) = stripForall (concl ith) in
      do corlist <- mapM ((repeatM rator `ffCombM` repeatM rator) <=<
                          destImp <=< body <=< rand) =<< 
                          liftM conjuncts (rand bod)
         consindex' <- mapM (\ v -> do w <- v `revAssoc` corlist
                                       r' <- w `assoc` consindex
                                       return (w, r')) avs
         recty <- liftM (head . snd) . destType . typeOf . fst . snd $
                    head consindex
         newtys <- mapM (liftM (head . snd) . destType . typeOf . snd . snd)
                     consindex'
         ptypes <- mapM (`mkFunTy` tyBool) newtys
         let preds = mkArgs "P" [] ptypes
             args = mkArgs "x" [] $ map (const recty) preds
         lambs <- map2M (\ (r, (m, _)) (p, a) ->
                         do l <- mkComb r a
                            cnj <- mkConj l =<< mkComb p =<< mkComb m a
                            mkAbs a cnj) consindex' $ zip preds args
         ruleSPECL lambs ith

pullbackInductionClause :: BoolCtxt thry => [(HOLThm, HOLThm)] -> [HOLThm] 
                        -> HOLThm -> HOLTerm -> HOL cls thry HOLThm
pullbackInductionClause tybijpairs conthms rthm tm =
    let (avs, bimp) = stripForall tm in
      case bimp of
        (ant :==> con) ->
            do ths <- mapM (ruleCONV convBETA) =<< 
                        ruleCONJUNCTS (primASSUME ant)
               (tths, pths) <- mapAndUnzipM ruleCONJ_PAIR ths
               tth <- ruleMATCH_MP (ruleSPEC_ALL rthm) $ foldr1M ruleCONJ tths
               mths <- mapM ruleIP (tth:tths)
               conth1 <- runConv convBETA con
               contm1 <- rand $ concl conth1
               cth2 <- runConv (convSUBS (tail mths)) =<< rand contm1
               conth2 <- primTRANS conth1 $ 
                           flip ruleAP_TERM cth2 =<< rator contm1
               conth3 <- rulePRE conth2
               let lctms = map concl pths
               lctms' <- listMkConj lctms
               asmin <- mkImp lctms' =<< rand =<< rand (concl conth3)
               argsin <- mapM rand =<< liftM conjuncts (lHand asmin)
               argsgen <- mapM (\ x -> 
                                  do xname <- fst `fmap` (destVar =<< rand x)
                                     return . mkVar xname $ typeOf x) argsin
               asmgen <- subst (zip argsin argsgen) asmin
               asmquant <- flip listMkForall asmgen =<< 
                             liftM (snd . stripComb) (rand =<< rand asmgen)
               th0 <- ruleSPEC_ALL $ primASSUME asmquant
               th1 <- primINST (zip argsgen argsin) th0
               th2 <- ruleMP th1 =<< foldr1M ruleCONJ pths
               th2' <- ruleCONJ tth th2
               th3 <- primEQ_MP (ruleSYM conth3) th2'
               ruleDISCH asmquant . ruleGENL avs $ ruleDISCH ant th3
        con ->
            do conth2 <- runConv convBETA con
               tth <- rulePART_MATCH return rthm =<< lHand =<< 
                        rand (concl conth2)
               conth3 <- rulePRE conth2
               asmgen <- rand =<< rand (concl conth3)
               asmquant <- flip listMkForall asmgen =<< 
                             liftM (snd . stripComb) (rand asmgen)
               th2 <- ruleSPEC_ALL $ primASSUME asmquant
               th2' <- ruleCONJ tth th2
               th3 <- primEQ_MP (ruleSYM conth3) th2'
               ruleDISCH asmquant =<< ruleGENL avs th3
  where rulePRE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        rulePRE thm = do thms <- mapM ruleSYM conthms 
                         ruleGEN_REWRITE (funpow 3 convRAND) thms thm
        
        ruleIP :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleIP thm = ruleSYM $ ruleGEN_REWRITE id (map snd tybijpairs) thm

finishInductionConclusion :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                          -> [(HOLThm, HOLThm)] -> HOLThm -> HOL cls thry HOLThm
finishInductionConclusion consindex tybijpairs th =
    do (_, bimp) <- destForall $ concl th
       pv <- lHand =<< body =<< rator =<< rand bimp
       (p, v) <- destComb pv
       (_, dest) <- p `assoc` consindex
       ty <- liftM (head . snd) . destType $ typeOf dest
       v' <- liftM (\ (x, _) -> mkVar x ty) $ destVar v
       dv <- mkComb dest v'
       th1 <- rulePRE =<< ruleSPEC dv th
       th2 <- ruleMP th1 $ primREFL =<< rand =<< lHand (concl th1)
       th3 <- ruleCONV convBETA th2
       ruleGEN v' =<< ruleFIN =<< ruleCONJUNCT2 th3
  where rulePRE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        rulePRE = let (tybij1, tybij2) = unzip tybijpairs in
                    ruleGEN_REWRITE (convLAND . convLAND . convRAND) tybij1 <=<
                    ruleGEN_REWRITE convLAND tybij2

        ruleFIN :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleFIN = let (tybij1, _) = unzip tybijpairs in
                    ruleGEN_REWRITE convRAND tybij1

deriveInductionTheorem :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                       -> [(HOLThm, HOLThm)] -> [HOLThm] -> HOLThm -> HOLThm 
                       -> HOL cls thry HOLThm
deriveInductionTheorem consindex tybijpairs conthms iith rth =
    do rths <- ruleCONJUNCTS rth
       bths <- map2M (pullbackInductionClause tybijpairs conthms) rths =<<
                 liftM conjuncts (lHand $ concl iith)
       asm <- listMkConj =<< mapM (lHand . concl) bths
       ths <- map2M ruleMP bths =<< ruleCONJUNCTS (primASSUME asm)
       th1 <- ruleMP iith $ foldr1M ruleCONJ ths
       th2 <- foldr1M ruleCONJ =<<
                mapM (finishInductionConclusion consindex tybijpairs) =<<
                  ruleCONJUNCTS th1
       th3 <- ruleDISCH asm th2
       preds <- mapM (rator <=< body <=< rand) =<< 
                  liftM conjuncts (rand $ concl th3)
       th4 <- ruleGENL preds th3
       pasms <- filterM (liftM (flip elem (map fst consindex)) .lHand) $ hyp th4
       th5 <- foldrM ruleDISCH th4 pasms
       (th6, _) <- foldrM ruleSCRUB_EQUATION (th5, []) $ hyp th5
       th7 <- ruleUNDISCH_ALL th6
       liftM fst . foldrM ruleSCRUB_EQUATION (th7, []) $ hyp th7

createRecursiveFunctions :: BoolCtxt thry => [(HOLThm, HOLThm)] 
                         -> [(HOLTerm, (HOLTerm, HOLTerm))] -> [HOLThm] 
                         -> HOLThm -> HOL cls thry HOLThm
createRecursiveFunctions tybijpairs consindex conthms rth =
    do domtys <- mapM (liftM (head . snd) . destType . typeOf . snd . snd) 
                   consindex
       recty <- liftM (head . snd) . destType . typeOf . fst . snd $ 
                   head consindex
       let ranty = mkVarType "Z"
       fnty <- mkFunTy recty ranty
       fn <- mkVar "fn" fnty
       fns <- liftM (mkArgs "fn" []) $ mapM (`mkFunTy` ranty) domtys
       let args = mkArgs "a" [] domtys
       rights <- map2M (\ (_, (_, d)) a ->
                   mkAbs a . mkComb fn $ mkComb d a) consindex args
       eqs <- map2M mkEq fns rights
       fdefs <- mapM primASSUME eqs
       fxths1 <- mapM (\ th1 -> tryFind (`primMK_COMB` th1) fdefs) conthms
       fxths2 <- mapM (\ th -> do th' <- runConv convBETA =<< rand (concl th)
                                  primTRANS th th') fxths1
       rths <- ruleCONJUNCTS rth
       fxths3 <- map2M simplifyFxthm rths fxths2
       fxths4 <- map2M (\ th1 -> primTRANS th1 . ruleAP_TERM fn) fxths2 fxths3
       fxth5 <- foldr1M ruleCONJ =<< map2M (cleanupFxthm fn) conthms fxths4
       pasms <- filterM (liftM (flip elem (map fst consindex)) . lHand) $
                  hyp fxth5
       fxth6 <- foldrM ruleDISCH fxth5 pasms
       (fxth7, _) <- foldrM ruleSCRUB_EQUATION (fxth6, []) $
                       foldr (union . hyp) [] conthms
       fxth8 <- ruleUNDISCH_ALL fxth7
       (fxth9, _) <- foldrM ruleSCRUB_EQUATION (fxth8, []) (hyp fxth8 \\ eqs)
       return fxth9

  where mkTybijcons :: (HOLThm, HOLThm) -> HOL cls thry HOLThm
        mkTybijcons (th1, th2) =
            do tms <- pairMapM (rand <=< lHand . concl) (th2, th1)
               th3 <- primINST [tms] th2
               c <- rator =<< lHand =<< rand (concl th2)
               th4 <- ruleAP_TERM c th1
               primEQ_MP (ruleSYM th3) th4

        convS :: BoolCtxt thry => Conversion cls thry
        convS = convGEN_REWRITE id (map mkTybijcons tybijpairs)

        ruleE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleE = ruleGEN_REWRITE id (map snd tybijpairs)

        simplifyFxthm :: BoolCtxt thry => HOLThm -> HOLThm 
                      -> HOL cls thry HOLThm
        simplifyFxthm rthm fxth =
          do pat <- funpowM 4 rand $ concl fxth
             rtm <- repeatM (liftM snd . destForall)$ concl rthm
             if isImp rtm
             then do th1 <- rulePART_MATCH (rand <=< rand) rthm pat
                     tms1 <- liftM conjuncts . lHand $ concl th1
                     ths2 <- mapM (\ t -> primEQ_MP (ruleSYM $ runConv convS t)
                                            thmTRUTH) tms1
                     ruleE =<< ruleMP th1 =<< foldr1M ruleCONJ ths2
             else ruleE =<< rulePART_MATCH rand rthm pat

        cleanupFxthm :: HOLTerm -> HOLThm -> HOLThm -> HOL cls thry HOLThm
        cleanupFxthm fn cth fxth =
            do tms <- liftM (snd . stripComb) $ rand =<< rand (concl fxth)
               kth <- ruleRIGHT_BETAS tms $ primASSUME (head $ hyp cth)
               primTRANS fxth $ ruleAP_TERM fn kth

createRecursionIsoConstructor :: WFCtxt thry
                              => [(HOLTerm, (HOLTerm, HOLTerm))] -> HOLThm 
                              -> HOL cls thry HOLTerm
createRecursionIsoConstructor consindex cth =
    do numty <- S.mkType "num" ([]::[HOLType])
       let zty = mkVarType "Z"
       s <- liftM (mkVar "s") $ mkFunTy numty zty
       recty <- liftM (head . snd) . destType . typeOf . fst $ head consindex
       domty <- liftM (head . snd) $ destType recty
       let i = mkVar"i" domty
       r <- liftM (mkVar "r") $ mkFunTy numty recty
       let mks = map (fst . snd) consindex
           mkindex = map (\ t -> (head . tail . snd . try' . destType $
                                  typeOf t, t)) mks
       artms <- (snd . stripComb) `fmap` (rand =<< rand (concl cth))
       artys <- mapFilterM (fmap typeOf . rand) artms
       (args, bod) <- liftM stripAbs . rand . head $ hyp cth
       (ccitm, rtm) <- destComb bod
       (_, itm) <- destComb ccitm
       let (rargs, iargs) = partition (`freeIn` rtm) args
       xths <- mapM (extractArg itm) iargs
       cargs' <- mapM (subst [(itm, i)] <=< lHand . concl) xths
       indices <- mapM sucivate [0..(length rargs - 1)]
       rindexed <- mapM (mkComb r) indices
       rargs' <- map2M (\ a rx -> flip mkComb rx =<<
                                    (a `assoc` mkindex)) artys rindexed
       sargs' <- mapM (mkComb s) indices
       let allargs = cargs' ++ rargs' ++ sargs'
       funty <- foldrM (mkFunTy . typeOf) zty allargs
       funname <- liftM fst $ destConst =<< repeatM rator =<< lHand (concl cth)
       let funarg = mkVar (funname `snoc` '\'') funty
       listMkAbs [i, r, s] =<< listMkComb funarg allargs           
  where extractArg :: PairCtxt thry => HOLTerm -> HOLTerm 
                   -> HOL cls thry HOLThm
        extractArg tup v
            | v == tup = primREFL tup
            | otherwise =
                do (t1, t2) <- destPair tup
                   thPAIR <- ruleISPECL [t1, t2] $ if v `freeIn` t1 then thmFST
                                                   else thmSND
                   tup' <- rand $ concl thPAIR
                   if tup' == v 
                      then return thPAIR
                      else ruleSUBS [ruleSYM thPAIR] =<< extractArg tup' v

deriveRecursionTheorem :: IndTypesPreCtxt thry
                       => [(HOLThm, HOLThm)] 
                       -> [(HOLTerm, (HOLTerm, HOLTerm))] -> [HOLThm] 
                       -> HOLThm -> HOL cls thry HOLThm
deriveRecursionTheorem tybijpairs consindex conthms rath =
    do isocons <- mapM (createRecursionIsoConstructor consindex) conthms
       let ty = typeOf $ head isocons
       fcons <- mkConst "FCONS" [(tyA, ty)]
       fnil <- mkConst "FNIL" [(tyA, ty)]
       bigfun <- foldrM (mkBinop fcons) fnil isocons
       eth <- ruleISPEC bigfun thmCONSTR_REC
       fn <- rator =<< rand (head . conjuncts $ concl rath)
       (v, bod) <- destAbs =<< rand (concl eth)
       betm <- varSubst [(v, fn)] bod
       fnths <- mapM (\ t -> do t' <- bndvar =<< rand t
                                ruleRIGHT_BETAS [t'] $ primASSUME t) $ hyp rath
       rthm <- foldr1M ruleCONJ =<< mapM (hackdownRath betm fnths) =<<
                 ruleCONJUNCTS rath
       let unseqs = filter isEq $ hyp rthm
       tys <- mapM (liftM (head . snd) . destType . typeOf . snd . snd) 
                consindex
       seqs <- mapM (\ x -> findM (\ t -> 
                 do t' <- lHand t
                    ty' <- liftM (head . snd) . destType $ typeOf t'
                    return $! ty' == x) unseqs) tys
       rethm <- foldrM ruleEXISTS_EQUATION rthm seqs
       fethm <- ruleCHOOSE fn eth rethm
       pcons <- mapM (repeatM rator <=< rand <=< 
                      repeatM (liftM snd . destForall)) . 
                  conjuncts $ concl rthm
       ruleGENL pcons fethm
  where convC :: IndTypesPreCtxt thry => Conversion cls thry
        convC = funpow 3 convRATOR . _REPEAT $ 
                  convGEN_REWRITE id [defFCONS]

        convL :: BoolCtxt thry => HOLTerm -> Conversion cls thry
        convL betm = convREWR (primASSUME betm)

        ruleSIMPER :: IndTypesPreCtxt thry => [HOLThm] -> HOLThm -> HOL cls thry HOLThm
        ruleSIMPER fnths th = 
            do ths1 <- mapM ruleSYM fnths
               let ths2 = map fst tybijpairs
               ths3 <- sequence [ thmFST, thmSND, thmBETA, defFCONS ]
               rulePURE_REWRITE (ths1++ths2++ths3) th

        hackdownRath :: IndTypesPreCtxt thry => HOLTerm -> [HOLThm] -> HOLThm 
                     -> HOL cls thry HOLThm
        hackdownRath betm fnths th =
            do (ltm, rtm) <- destEq $ concl th
               (_, wargs) <- stripComb `fmap` rand ltm
               th0 <- runConv (convL betm) rtm
               th1 <- primTRANS th th0
               th1' <- runConv convC =<< rand (concl th1)
               th2 <- primTRANS th1 th1'
               th2' <- runConv (funpow 2 convRATOR convBETA) =<< 
                         rand (concl th2)
               th3 <- primTRANS th2 th2'
               th3' <- runConv (convRATOR convBETA) =<< rand (concl th3)
               th4 <- primTRANS th3 th3'
               th4' <- runConv convBETA =<< rand (concl th4)
               th5 <- primTRANS th4 th4'
               ruleGENL wargs $ ruleSIMPER fnths th5


parseInductiveTypeSpecification :: MonadThrow m => ParseContext -> Text 
                                -> m [(HOLType, [(Text, [HOLType])])]
parseInductiveTypeSpecification ctxt s =
     mapM toTys =<< runHOLParser parser ctxt s
  where parser :: MyParser [(Text, [(Text, [PreType])])]
        parser = mywhiteSpace >> mysemiSep1 typeParser
        
        typeParser :: MyParser (Text, [(Text, [PreType])])
        typeParser = do x <- myidentifier
                        myreservedOp "="
                        ptys <- subtypeParser `mysepBy1` myreservedOp "|"
                        return (x, ptys)

        subtypeParser :: MyParser (Text, [PreType])
        subtypeParser = do x <- myidentifier
                           ptys <- mymany ptype
                           return (x, ptys)

        toTys :: MonadThrow m => (Text, [(Text, [PreType])]) -> 
                 m (HOLType, [(Text, [HOLType])])
        toTys (s', ptys) = 
            let ty = mkVarType s' in
              do tys <- mapM (\ (x, y) -> do y' <- mapM (tyElab ctxt) y
                                             return (x, y')) ptys
                 return (ty, tys)

{- Basic version of defineTypeRaw.  
   Returns the induction and recursion theorems separately.
   The parser isn't used.
-}
defineTypeRaw :: IndTypesPreCtxt thry
              => [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw def =
    do (defs, rth, ith) <- justifyInductiveTypeModel def
       neths <- proveModelInhabitation rth
       tybijpairs <- mapM (defineInductiveType defs) neths
       preds <- mapM (repeatM rator . concl) neths
       mkdests <- mapM (\ (th, _) -> do tm <- lHand $ concl th
                                        tm' <- rand tm
                                        pairMapM rator (tm, tm')) tybijpairs
       let consindex = zip preds mkdests
       condefs <- mapM (defineInductiveTypeConstructor defs consindex) =<<
                    ruleCONJUNCTS rth
       conthms <- mapM (\ th@(Thm _ c) -> 
                            do cs <- (fst . stripAbs) `fmap` rand c
                               ruleRIGHT_BETAS cs th) condefs
       iith <- instantiateInductionTheorem consindex ith
       fth <- deriveInductionTheorem consindex tybijpairs conthms iith rth
       rath <- createRecursiveFunctions tybijpairs consindex conthms rth
       kth <- deriveRecursionTheorem tybijpairs consindex conthms rath
       return (fth, kth)
