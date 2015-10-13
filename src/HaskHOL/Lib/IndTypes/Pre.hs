{-# LANGUAGE FlexibleContexts #-}
module HaskHOL.Lib.IndTypes.Pre where

import HaskHOL.Core hiding (many, rights)
import HaskHOL.Deductive hiding (getDefinition, getSpecification, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.WF

sucivate :: Int -> HOL cls thry HOLTerm
sucivate n =
    do zero <- toHTm "0"
       suc <- toHTm "SUC"
       liftEither "sucivate" $ funpowM n (mkComb suc) zero

ruleSCRUB_EQUATION :: BoolCtxt thry => HOLTerm -> (HOLThm, HOLTermEnv) 
                   -> HOL cls thry (HOLThm, HOLTermEnv)
ruleSCRUB_EQUATION eq (th, insts) =
    do eq' <- liftO $ foldrM subst eq (map (: []) insts)
       let (l, r) = fromJust $ destEq eq'
       th' <- ruleDISCH eq' th
       th'' <- flip ruleMP (primREFL r) #<< primINST [(l, r)] th'
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
       let bottail = fromRight $ mkAbs nTm bot
       --
           mkConstructor :: Int -> (Text, [HOLType]) -> HOL cls thry HOLTerm
           mkConstructor n (cname, cargs) =
            let ttys = map (\ ty -> if ty `elem` newtys 
                                    then recty else ty) cargs
                args = mkArgs "a" [] ttys
                (rargs, iargs) = partition (\ t -> typeOf t == recty) args
                --
                mkInjector :: [HOLTerm] -> [HOLType] -> [HOLTerm] 
                           -> Maybe [HOLTerm]
                mkInjector _ [] _ = return []
                mkInjector (tm:tms) (ty:tys) is =
                    (do (a, iargs') <- remove (\ t -> typeOf t == ty) is
                        tl <- mkInjector tms tys iargs'
                        return (a:tl))
                    <|> (do tl <- mkInjector tms tys is
                            return (tm:tl))
                mkInjector _ _ _ = Nothing in
                --
              do iarg <- (foldr1M mkPair #<< mkInjector epstms alltys iargs) <|>
                           return bepsTm
                 let rarg = fromRight $ foldrM (mkBinop fcons) bottail rargs
                 conty <- foldrM mkFunTy recty $ map typeOf args
                 n' <- sucivate n
                 let condef = fromRight $ listMkComb constr [n', iarg, rarg]
                 mkEq (mkVar cname conty) #<< listMkAbs args condef
       --         
           mkConstructors :: Int -> [(Text, [HOLType])] 
                          -> HOL cls thry [HOLTerm]
           mkConstructors _ [] = return []
           mkConstructors n (x:xs) =
            do hd <- mkConstructor n x
               tl <- mkConstructors (n + 1) xs
               return (hd:tl)
       --
       condefs <- mkConstructors 0 $ concat rights
       let conths = fromRight $ mapM primASSUME condefs
       predty <- mkFunTy recty tyBool
       let edefs = foldr (\ (x, l) acc -> map (\ t -> (x, t)) l ++ acc) [] def
           idefs = fromJust $ map2 (\ (r, (_, atys)) d -> 
                                    ((r, atys), d)) edefs condefs
       --  
           mkRule :: ((HOLType, [HOLType]), HOLTerm) 
                  -> HOL cls thry HOLTerm
           mkRule ((r, a), condef) =
            let (left, right) = fromJust $ destEq condef
                (args, _) = stripAbs right
                (conc, conds) = fromRight $
                  do lapp <- listMkComb left args
                     conds' <- foldr2M (\ arg argty sofar ->
                                if argty `elem` newtys
                                then do ty' <- note "" $ destVarType argty 
                                        arg' <- mkComb (mkVar ty' predty) arg
                                        return (arg':sofar)
                                else return sofar) [] args a
                     ty' <- note "" $ destVarType r
                     conc' <- mkComb (mkVar ty' predty) lapp
                     return (conc', conds') in
              do rule <- if null conds then return conc
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
        munion s1 = fromJust . munion' s1
        
        munion' :: Eq a => [a] -> [a] -> Maybe [a]
        munion' [] s2 = Just s2
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
           concs = map concl bases ++ map (fromJust . rand . concl) imps
           preds = setify . fromJust $ mapM (repeatM rator) concs
       ithms <- exhaustInhabitations imps bases
       liftO $ mapM (\ p -> find 
                     (\ th -> (fst . stripComb $ concl th) == p) ithms) preds
           
  where exhaustInhabitations :: BoolCtxt thry => [HOLThm] -> [HOLThm] 
                             -> HOL cls thry [HOLThm]
        exhaustInhabitations ths sofar =
            let dunnit = setify $ map (fst . stripComb . concl) sofar
                useful = filter (\ (Thm _ c) -> 
                                 (fst . stripComb . fromJust $ rand c)
                                  `notElem` dunnit) ths in
              if null useful then return sofar
              else do newth <- tryFind followHorn useful
                      exhaustInhabitations ths (newth:sofar)
          where followHorn :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
                followHorn thm@(Thm _ c) =
                    let preds = map (fst . stripComb) . conjuncts . fromJust $ 
                                  lHand c
                        asms = fromJust $ mapM (\ p -> find 
                                 (\ (Thm _ c') ->  fst (stripComb c') == p) 
                                   sofar) preds in
                      ruleMATCH_MP thm =<< foldr1M ruleCONJ asms
                followHorn _ = error "followHorn: exhaustive warning."

defineInductiveType :: BoolCtxt thry => [HOLThm] -> HOLThm 
                    -> HOL Theory thry (HOLThm, HOLThm)
defineInductiveType cdefs exth@(Thm asl extm) =
    let (epred@(Var ename _), _) = stripComb extm
        th1@(Thm _ c1) = fromRight $ primASSUME #<< 
                           find (\ eq -> lHand eq == Just epred) asl in
      do th1' <- runConv (convSUBS cdefs) #<< rand c1
         let th2 = fromRight $ primTRANS th1 th1'
             th2' = fromRight $ ruleAP_THM th2 #<< rand extm
             th3@(Thm asl3 _) = fromRight $ primEQ_MP th2' exth
         (th4, _) <- foldrM ruleSCRUB_EQUATION (th3, []) asl3
         let mkname = "_mk_" `append` ename
             destname = "_dest_" `append` ename
         (bij1, bij2@(Thm _ bc)) <- newBasicTypeDefinition ename mkname destname
                                     th4
         let bij2a = fromRight $ ruleAP_THM th2 #<< rand =<< rand bc
             bij2b = fromRight $ primTRANS bij2a bij2
         return (bij1, bij2b)
defineInductiveType _ _ = error "defineInductiveType: exhaustive warning."

defineInductiveTypeConstructor :: PairCtxt thry => [HOLThm] 
                               -> [(HOLTerm, (HOLTerm, HOLTerm))] 
                               -> HOLThm -> HOL Theory thry HOLThm
defineInductiveTypeConstructor defs consindex (Thm _ c) =
    let (_, bod) = stripForall c
        (defrt, expth, deflf@(Var name _)) = fromJust $
            do asms <- if isImp bod then liftM conjuncts $ lHand bod 
                       else return []
               conc <- if isImp bod then rand bod else return bod
               asmlist <- mapM destComb asms
               (cpred, cterm) <- destComb conc
               let (oldcon, oldargs) = stripComb cterm
               (newrights, newargs) <- mapAndUnzipM (modifyArg asmlist) oldargs
               (retmk, _) <- cpred `lookup` consindex
               defbod <- hush $ mkComb retmk =<< listMkComb oldcon newrights
               defrt' <- hush $ listMkAbs newargs defbod
               expth' <- find (\ (Thm _ c') -> lHand c' == Just oldcon) defs
               deflf' <- liftM (\ (x, _) -> mkVar x $ typeOf defrt') $ 
                           destVar oldcon
               return (defrt', expth', deflf') in
      do rexpth <- runConv (convSUBS [expth]) defrt
         deftm <- mkEq deflf #<< rand (concl rexpth)
         defth <- newDefinition (name, deftm)
         liftO $ primTRANS defth =<< ruleSYM rexpth
  where modifyArg :: HOLTermEnv -> HOLTerm -> Maybe (HOLTerm, HOLTerm)
        modifyArg asmlist v =
            (do (_, dest) <- liftM1 lookup (v `revLookup` asmlist) consindex
                ty' <- liftM (head . snd) . destType $ typeOf dest
                v' <- liftM (\ (x, _) -> mkVar x ty') $ destVar v
                v'' <- hush $ mkComb dest v'
                return (v'', v'))
            <|> return (v, v)
defineInductiveTypeConstructor _ _ _ = 
    error "defineInductiveTypeConstructor: exhaustive warning."

instantiateInductionTheorem :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                            -> HOLThm -> HOL cls thry HOLThm
instantiateInductionTheorem consindex ith@(Thm _ c) =
    let (avs, bod) = stripForall c
        (consindex', recty, newtys) = fromJust $
          do corlist <- mapM ((repeatM rator `ffCombM` repeatM rator) <=<
                               destImp <=< body <=< rand) =<< 
                          liftM conjuncts (rand bod)
             consindex'' <- mapM (\ v -> do w <- v `revLookup` corlist
                                            r' <- w `lookup` consindex
                                            return (w, r')) avs
             recty' <- liftM (head . snd) . destType . typeOf . fst . snd $
                         head consindex
             newtys' <- mapM (liftM (head . snd) . destType . typeOf . snd . snd)
                          consindex''
             return (consindex'', recty', newtys') in
      do ptypes <- mapM (`mkFunTy` tyBool) newtys
         let preds = mkArgs "P" [] ptypes
             args = mkArgs "x" [] $ map (const recty) preds
         lambs <- map2M (\ (r, (m, _)) (p, a) ->
                         let l = fromRight $ mkComb r a in
                           do cnj <- mkConj l #<< mkComb p =<< mkComb m a
                              liftO $ mkAbs a cnj) consindex' $ zip preds args
         ruleSPECL lambs ith
instantiateInductionTheorem _ _ =
    error "instantiateInductionTheorem: exhaustive warning."

pullbackInductionClause :: BoolCtxt thry => [(HOLThm, HOLThm)] -> [HOLThm] 
                        -> HOLThm -> HOLTerm -> HOL cls thry HOLThm
pullbackInductionClause tybijpairs conthms rthm tm =
    let (avs, bimp) = stripForall tm in
      case bimp of
        (ant :==> con) ->
            do ths <- mapM (ruleCONV convBETA) =<< ruleCONJUNCTS #<< 
                        primASSUME ant
               (tths, pths) <- mapAndUnzipM ruleCONJ_PAIR ths
               tth <- liftM1 ruleMATCH_MP (ruleSPEC_ALL rthm) =<< 
                        foldr1M ruleCONJ tths
               mths <- mapM ruleIP (tth:tths)
               conth1 <- runConv convBETA con
               let contm1 = fromJust . rand $ concl conth1
               cth2 <- runConv (convSUBS (tail mths)) #<< rand contm1
               let conth2 = fromRight $ primTRANS conth1 =<< 
                              flip ruleAP_TERM cth2 #<< rator contm1
               conth3 <- rulePRE conth2
               let lctms = map concl pths
               asmin <- liftM1 mkImp (listMkConj lctms) #<< rand =<< 
                          rand (concl conth3)
               let argsin = fromJust $ mapM rand =<< 
                              liftM conjuncts (lHand asmin)
                   argsgen = map (\ x -> 
                                  mkVar (fst . fromJust $ destVar =<< rand x) $
                                    typeOf x) argsin
               asmgen <- liftO $ subst (zip argsin argsgen) asmin
               asmquant <- flip listMkForall asmgen #<< 
                             liftM (snd . stripComb) (rand =<< rand asmgen)
               th0 <- ruleSPEC_ALL #<< primASSUME asmquant
               let th1 = fromJust $ primINST (zip argsgen argsin) th0
               th2 <- ruleMP th1 =<< foldr1M ruleCONJ pths
               th2' <- ruleCONJ tth th2
               let th3 = fromRight $ liftM1 primEQ_MP (ruleSYM conth3) th2'
               ruleDISCH asmquant =<< ruleGENL avs =<< ruleDISCH ant th3
        con ->
            do conth2 <- runConv convBETA con
               tth <- rulePART_MATCH return rthm #<< 
                        lHand =<< rand (concl conth2)
               conth3 <- rulePRE conth2
               let asmgen = fromJust $ rand =<< rand (concl conth3)
               asmquant <- flip listMkForall asmgen #<< 
                             liftM (snd . stripComb) (rand asmgen)
               th2 <- ruleSPEC_ALL #<< primASSUME asmquant
               th2' <- ruleCONJ tth th2
               let th3 = fromRight $ liftM1 primEQ_MP (ruleSYM conth3) th2'
               ruleDISCH asmquant =<< ruleGENL avs th3
  where rulePRE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        rulePRE thm = let thms = fromRight $ mapM ruleSYM conthms in
                        ruleGEN_REWRITE (funpow 3 convRAND) thms thm
        
        ruleIP :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleIP thm = do thm' <- ruleGEN_REWRITE id (map snd tybijpairs) thm
                        liftO $ ruleSYM thm'

finishInductionConclusion :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                          -> [(HOLThm, HOLThm)] -> HOLThm -> HOL cls thry HOLThm
finishInductionConclusion consindex tybijpairs th@(Thm _ c) =
    let (v', dv) = fromJust $
          do (_, bimp) <- destForall c
             pv <- lHand =<< body =<< rator =<< rand bimp
             (p, v) <- destComb pv
             (_, dest) <- p `lookup` consindex
             ty <- liftM (head . snd) . destType $ typeOf dest
             v'' <- liftM (\ (x, _) -> mkVar x ty) $ destVar v
             dv' <- hush $ mkComb dest v''
             return (v'', dv') in
      do th1 <- rulePRE =<< ruleSPEC dv th
         th2 <- ruleMP th1 #<< liftM primREFL (rand =<< lHand (concl th1))
         th3 <- ruleCONV convBETA th2
         ruleGEN v' =<< ruleFIN =<< ruleCONJUNCT2 th3
  where rulePRE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        rulePRE = let (tybij1, tybij2) = unzip tybijpairs in
                    ruleGEN_REWRITE (convLAND . convLAND . convRAND) tybij1 <=<
                    ruleGEN_REWRITE convLAND tybij2

        ruleFIN :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleFIN = let (tybij1, _) = unzip tybijpairs in
                    ruleGEN_REWRITE convRAND tybij1
finishInductionConclusion _ _ _ =
   error "finishInductionConclusion: exhaustive warning."

deriveInductionTheorem :: BoolCtxt thry => [(HOLTerm, (HOLTerm, HOLTerm))] 
                       -> [(HOLThm, HOLThm)] -> [HOLThm] -> HOLThm -> HOLThm 
                       -> HOL cls thry HOLThm
deriveInductionTheorem consindex tybijpairs conthms iith rth =
    do bths <- liftM1 (map2M (pullbackInductionClause tybijpairs conthms))
                 (ruleCONJUNCTS rth) #<< liftM conjuncts (lHand $ concl iith)
       asm <- listMkConj #<< mapM (lHand . concl) bths
       ths <- map2M ruleMP bths =<< ruleCONJUNCTS #<< primASSUME asm
       th1 <- ruleMP iith =<< foldr1M ruleCONJ ths
       th2 <- foldr1M ruleCONJ =<< 
                mapM (finishInductionConclusion consindex tybijpairs) =<<
                  ruleCONJUNCTS th1
       th3 <- ruleDISCH asm th2
       let preds = fromJust $ mapM (rator <=< body <=< rand) =<< 
                     liftM conjuncts (rand $ concl th3)
       th4 <- ruleGENL preds th3
       let pasms = filter (flip elem (map fst consindex) . fromJust . lHand) $
                     hyp th4
       th5 <- foldrM ruleDISCH th4 pasms
       (th6, _) <- foldrM ruleSCRUB_EQUATION (th5, []) $ hyp th5
       th7 <- ruleUNDISCH_ALL th6
       liftM fst . foldrM ruleSCRUB_EQUATION (th7, []) $ hyp th7

createRecursiveFunctions :: BoolCtxt thry => [(HOLThm, HOLThm)] 
                         -> [(HOLTerm, (HOLTerm, HOLTerm))] -> [HOLThm] 
                         -> HOLThm -> HOL cls thry HOLThm
createRecursiveFunctions tybijpairs consindex conthms rth =
    let domtys = map (head . snd . fromJust . destType . typeOf . snd . snd) 
                   consindex
        recty = (head . snd . fromJust . destType . typeOf . fst . snd . head)
                  consindex
        ranty = mkVarType "Z" in
      do fn <- liftM (mkVar "fn") $ mkFunTy recty ranty
         fns <- liftM (mkArgs "fn" []) $ mapM (`mkFunTy` ranty) domtys
         let args = mkArgs "a" [] domtys
             rights = fromRight $ 
                        map2M (\ (_, (_, d)) a -> mkAbs a =<< 
                               mkComb fn =<< mkComb d a) consindex args
         eqs <- map2M mkEq fns rights
         let fdefs = fromRight $ mapM primASSUME eqs
             fxths1 = fromRight $ 
                        mapM (\ th1 -> tryFind 
                              (`primMK_COMB` th1) fdefs) conthms
         fxths2 <- mapM (\ th -> do th' <- runConv convBETA #<< rand (concl th)
                                    liftO $ primTRANS th th') fxths1
         fxths3 <- liftM1 (map2M simplifyFxthm) (ruleCONJUNCTS rth) fxths2
         let fxths4 = fromRight $ 
                        map2M (\ th1 -> primTRANS th1 <=< ruleAP_TERM fn) fxths2
                          fxths3
         fxth5 <- foldr1M ruleCONJ =<< map2M (cleanupFxthm fn) conthms fxths4
         let pasms = filter (flip elem (map fst consindex) . fromJust . lHand) $
                       hyp fxth5
         fxth6 <- foldrM ruleDISCH fxth5 pasms
         (fxth7, _) <- foldrM ruleSCRUB_EQUATION (fxth6, []) $
                         foldr (union . hyp) [] conthms
         fxth8 <- ruleUNDISCH_ALL fxth7
         (fxth9, _) <- foldrM ruleSCRUB_EQUATION (fxth8, []) (hyp fxth8 \\ eqs)
         return fxth9

  where mkTybijcons :: (HOLThm, HOLThm) -> Either String HOLThm
        mkTybijcons (th1, th2) =
            do tms <- note "" $ pairMapM (rand <=< lHand . concl) (th2, th1)
               th3 <- note "" $ primINST [tms] th2
               th4 <- flip ruleAP_TERM th1 #<< rator =<< lHand =<< 
                        rand (concl th2)
               liftM1 primEQ_MP (ruleSYM th3) th4

        convS :: BoolCtxt thry => Conversion cls thry
        convS = convGEN_REWRITE id (fromRight $ mapM mkTybijcons tybijpairs)

        ruleE :: BoolCtxt thry => HOLThm -> HOL cls thry HOLThm
        ruleE = ruleGEN_REWRITE id (map snd tybijpairs)

        simplifyFxthm :: BoolCtxt thry => HOLThm -> HOLThm 
                      -> HOL cls thry HOLThm
        simplifyFxthm rthm fxth =
            let pat = fromJust . funpowM 4 rand $ concl fxth
                rtm = fromJust . repeatM (liftM snd . destForall)$ concl rthm in
              if isImp rtm
              then do th1 <- rulePART_MATCH (rand <=< rand) rthm pat
                      let tms1 = conjuncts . fromJust . lHand $ concl th1
                      ths2 <- mapM (\ t -> do tth <- thmTRUTH
                                              th <- runConv convS t
                                              liftO $ liftM1 primEQ_MP 
                                                (ruleSYM th) tth) tms1
                      ruleE =<< ruleMP th1 =<< foldr1M ruleCONJ ths2
              else ruleE =<< rulePART_MATCH rand rthm pat

        cleanupFxthm :: HOLTerm -> HOLThm -> HOLThm -> HOL cls thry HOLThm
        cleanupFxthm fn cth fxth =
            let tms = snd . stripComb . fromJust $ rand =<< rand (concl fxth) in
              do kth <- ruleRIGHT_BETAS tms #<< primASSUME (head $ hyp cth)
                 liftO $ primTRANS fxth =<< ruleAP_TERM fn kth

createRecursionIsoConstructor :: WFCtxt thry
                              => [(HOLTerm, (HOLTerm, HOLTerm))] -> HOLThm 
                              -> HOL cls thry HOLTerm
createRecursionIsoConstructor consindex cth =
    do numty <- mkType "num" []
       let zty = mkVarType "Z"
       s <- liftM (mkVar "s") $ mkFunTy numty zty
       let recty = head . snd . fromJust . destType . typeOf . fst $ 
                     head consindex
           domty = head . snd . fromJust $ destType recty
           i = mkVar"i" domty
       r <- liftM (mkVar "r") $ mkFunTy numty recty
       let mks = map (fst . snd) consindex
           mkindex = map (\ t -> (head . tail . snd . fromJust . destType $
                                    typeOf t, t)) mks
           artms = snd . stripComb . fromJust $ rand =<< rand (concl cth)
           artys = mapFilter (liftM typeOf . rand) artms
           (args, bod) = stripAbs . fromJust . rand . head $ hyp cth
           (ccitm, rtm) = fromJust $ destComb bod
           (_, itm) = fromJust $ destComb ccitm
           (rargs, iargs) = partition (`freeIn` rtm) args
       xths <- mapM (extractArg itm) iargs
       cargs' <- liftO $ mapM (subst [(itm, i)] <=< lHand . concl) xths
       indices <- mapM sucivate [0..(length rargs - 1)]
       let rindexed = fromRight $ mapM (mkComb r) indices
           rargs' = fromRight $ map2M (\ a rx -> flip mkComb rx #<<
                                      (a `lookup` mkindex)) artys rindexed
           sargs' = fromRight $ mapM (mkComb s) indices
           allargs = cargs' ++ rargs' ++ sargs'
       funty <- foldrM (mkFunTy . typeOf) zty allargs
       let funname = fst . fromJust $ destConst =<< repeatM rator =<< 
                       lHand (concl cth)
           funarg = mkVar (funname `snoc` '\'') funty
       liftO $ listMkAbs [i, r, s] =<< listMkComb funarg allargs           
  where extractArg :: PairCtxt thry => HOLTerm -> HOLTerm 
                   -> HOL cls thry HOLThm
        extractArg tup v
            | v == tup = return $ primREFL tup
            | otherwise =
                let (t1, t2) = fromJust $ destPair tup in
                  do thPAIR <- ruleISPECL [t1, t2] $ if v `freeIn` t1 
                                                     then thmFST
                                                     else thmSND
                     let tup' = fromJust . rand $ concl thPAIR
                     if tup' == v 
                        then return thPAIR
                        else do th <- extractArg tup' v
                                ruleSUBS [ruleSYM thPAIR] th

deriveRecursionTheorem :: (HOLThmRep thm cls thry, WFCtxt thry) 
                       => thm 
                       -> [(HOLThm, HOLThm)] 
                       -> [(HOLTerm, (HOLTerm, HOLTerm))] -> [HOLThm] 
                       -> HOLThm -> HOL cls thry HOLThm
deriveRecursionTheorem thmCONSTR_REC tybijpairs consindex conthms rath =
    do isocons <- mapM (createRecursionIsoConstructor consindex) conthms
       let ty = typeOf $ head isocons
       fcons <- mkConst "FCONS" [(tyA, ty)]
       fnil <- mkConst "FNIL" [(tyA, ty)]
       let bigfun = fromRight $ foldrM (mkBinop fcons) fnil isocons
       eth <- ruleISPEC bigfun thmCONSTR_REC
       let fn = fromJust $ rator =<< rand (head . conjuncts $ concl rath)
           betm = fromJust $ 
                    do (v, bod) <- destAbs =<< rand (concl eth)
                       varSubst [(v, fn)] bod
       fnths <- mapM (\ t -> ruleRIGHT_BETAS [fromJust $ bndvar =<< rand t] #<< 
                               primASSUME t) $ hyp rath
       rthm <- foldr1M ruleCONJ =<< mapM (hackdownRath betm fnths) =<<
                 ruleCONJUNCTS rath
       let seqs = fromJust $
                    let unseqs = filter isEq $ hyp rthm in
                      do tys <- mapM (liftM (head . snd) . destType . typeOf .
                                      snd . snd) consindex
                         mapM (\ x -> findM
                               (\ t -> do t' <- lHand t
                                          ty' <- liftM (head . snd) . destType $
                                                   typeOf t'
                                          return $! ty' == x) unseqs) tys
       rethm <- foldrM ruleEXISTS_EQUATION rthm seqs
       fethm <- ruleCHOOSE fn eth rethm
       let pcons = fromJust . mapM (repeatM rator <=< rand <=< 
                                    repeatM (liftM snd . destForall)) . 
                     conjuncts $ concl rthm
       ruleGENL pcons fethm
  where convC :: BoolCtxt thry => Conversion cls thry
        convC = funpow 3 convRATOR . _REPEAT $ 
                  convGEN_REWRITE id [getDefinition "FCONS"]

        convL :: BoolCtxt thry => HOLTerm -> Conversion cls thry
        convL betm = convREWR (primASSUME betm)

        ruleSIMPER :: PairCtxt thry => [HOLThm] -> HOLThm -> HOL cls thry HOLThm
        ruleSIMPER fnths th = 
            let ths1 = fromRight $ mapM ruleSYM fnths
                ths2 = map fst tybijpairs in
              do ths3 <- sequence [ thmFST, thmSND, thmBETA
                                  , getDefinition "FCONS" ]
                 rulePURE_REWRITE (ths1++ths2++ths3) th

        hackdownRath :: PairCtxt thry => HOLTerm -> [HOLThm] -> HOLThm 
                     -> HOL cls thry HOLThm
        hackdownRath betm fnths th =
            let (ltm, rtm) = fromJust . destEq $ concl th
                wargs = snd . stripComb . fromJust $ rand ltm in
              do th0 <- runConv (convL betm) rtm
                 let th1 = fromRight $ primTRANS th th0
                 th1' <- runConv convC #<< rand (concl th1)
                 let th2 = fromRight $ primTRANS th1 th1'
                 th2' <- runConv (funpow 2 convRATOR convBETA) #<< 
                           rand (concl th2)
                 let th3 = fromRight $ primTRANS th2 th2'
                 th3' <- runConv (convRATOR convBETA) #<< rand (concl th3)
                 let th4 = fromRight $ primTRANS th3 th3'
                 th4' <- runConv convBETA #<< rand (concl th4)
                 let th5 = fromRight $ primTRANS th4 th4'
                 ruleGENL wargs =<< ruleSIMPER fnths th5


parseInductiveTypeSpecification :: ParseContext -> Text -> Either String [(HOLType, [(Text, [HOLType])])]
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

        toTys :: (Text, [(Text, [PreType])]) -> 
                 Either String (HOLType, [(Text, [HOLType])])
        toTys (s', ptys) = 
            let ty = mkVarType s' in
              do tys <- mapM (\ (x, y) -> do y' <- mapM (tyElab ctxt) y
                                             return (x, y')) ptys
                 return (ty, tys)

{- Basic version of defineTypeRaw.  
   Returns the induction and recursion theorems separately.
   The parser isn't used.
-}
defineTypeRaw :: (HOLThmRep thm Theory thry, WFCtxt thry) 
              => thm 
              -> [(HOLType, [(Text, [HOLType])])] 
              -> HOL Theory thry (HOLThm, HOLThm)
defineTypeRaw thmCONSTR_REC def =
    do (defs, rth, ith) <- justifyInductiveTypeModel def
       neths <- proveModelInhabitation rth
       tybijpairs <- mapM (defineInductiveType defs) neths
       let preds = fromJust $ mapM (repeatM rator . concl) neths
           mkdests = fromJust $ mapM (\ (th, _) -> do tm <- lHand $ concl th
                                                      tm' <- rand tm
                                                      pairMapM rator (tm, tm')) 
                                  tybijpairs
           consindex = zip preds mkdests
       condefs <- mapM (defineInductiveTypeConstructor defs consindex) =<<
                    ruleCONJUNCTS rth
       conthms <- mapM (\ th -> let args = fst . stripAbs . fromJust . rand $ 
                                             concl th in
                                  ruleRIGHT_BETAS args th) condefs
       iith <- instantiateInductionTheorem consindex ith
       fth <- deriveInductionTheorem consindex tybijpairs conthms iith rth
       rath <- createRecursiveFunctions tybijpairs consindex conthms rth
       kth <- deriveRecursionTheorem thmCONSTR_REC tybijpairs consindex conthms rath
       return (fth, kth)
