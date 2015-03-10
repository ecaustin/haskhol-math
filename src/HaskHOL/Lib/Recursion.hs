{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
{-|
  Module:    HaskHOL.Lib.Recursion
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Recursion
    ( newRecursiveDefinition
    , getRecursiveDefinition
    , proveRecursiveFunctionsExist
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newSpecification)

import HaskHOL.Lib.Nums

data TheRecursiveDefinitions = 
    TheRecursiveDefinitions !(Map String HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''TheRecursiveDefinitions

insertDefinition :: String -> HOLThm -> Update TheRecursiveDefinitions ()
insertDefinition lbl thm =
    do TheRecursiveDefinitions defs <- get
       put (TheRecursiveDefinitions (mapInsert lbl thm defs))

getDefinitions :: Query TheRecursiveDefinitions [HOLThm]
getDefinitions =
    do TheRecursiveDefinitions defs <- ask
       return $! mapElems defs

getADefinition :: String -> Query TheRecursiveDefinitions (Maybe HOLThm)
getADefinition name =
    do (TheRecursiveDefinitions defs) <- ask
       return $! name `mapLookup` defs

makeAcidic ''TheRecursiveDefinitions 
    ['insertDefinition, 'getDefinitions, 'getADefinition]


proveRawRecursiveFunctionsExist :: BoolCtxt thry => HOLThm -> HOLTerm 
                                -> HOL cls thry HOLThm
proveRawRecursiveFunctionsExist ax tm =
    let rawcls = conjuncts tm
        spcls = map (snd . stripForall) rawcls
        lpats = fromJust $ mapM (liftM stripComb . lHand) spcls
        ufns = itlist (insert . fst) lpats [] in
      do axth <- ruleSPEC_ALL ax
         let (exvs, axbody) = stripExists $ concl axth
             axcls = conjuncts axbody
             f = liftM fst . (destConst <=< repeatM rator <=< rand <=<
                              lHand . snd . stripForall)
             findax (x, _) = lookup x =<< mapM (\ t -> do f' <- f t
                                                          return (f', t)) axcls
         (raxs, axfns) <- liftMaybe ("proveRawRecursiveFunctionsExist: " ++ 
                                     "failed to find.") $
                            do raxs <- mapM (findax <=< destConst <=< 
                                             repeatM rator . head . snd) lpats
                               axfns <- mapM (repeatM rator <=< lHand . snd .
                                              stripForall) raxs
                               return (raxs, axfns)
         let urfns = 
                 map (\ v -> lookupd v (setify . zip axfns $ map fst lpats) v) 
                   exvs
         axtm <- listMkExists exvs =<< listMkConj raxs
         urtm <- listMkExists urfns tm
         insts <- liftO $ termMatch [] axtm urtm
         ixth <- ruleINSTANTIATE insts axth
         let (ixvs, ixbody) = stripExists $ concl ixth
         ixtm <- liftO $ subst (zip ixvs urfns) ixbody
         ixths <- ruleCONJUNCTS #<< primASSUME ixtm
         let rixths = fromJust $ 
                        mapM (\ t -> find (aConv t . concl) ixths) rawcls
         rixth <- itlistM ruleSIMPLE_EXISTS ufns =<< 
                    foldr1M ruleCONJ rixths
         rixth' <- foldrM ruleSIMPLE_CHOOSE rixth urfns
         return $ rulePROVE_HYP ixth rixth'
                   

canonize :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
canonize t =
    let (avs, bod) = stripForall t
        (l, r) = fromJust $ destEq bod
        (fn, rarg:vargs) = stripComb l
        l' = fromRight $ mkComb fn rarg in
      do r' <- liftEither "canonize: failed to build abstraction." $
                 listMkAbs vargs r
         let fvs = frees rarg
         t' <- listMkForall fvs =<< mkEq l' r'
         ruleGENL avs =<< ruleRIGHT_BETAS vargs =<< ruleSPECL fvs #<< 
           primASSUME t'
         

proveCanonRecursiveFunctionsExist :: BoolCtxt thry => HOLThm -> HOLTerm 
                                  -> HOL cls thry HOLThm
proveCanonRecursiveFunctionsExist ax tm =
    do ths <- mapM canonize $ conjuncts tm
       atm <- listMkConj $ map (head . hyp) ths
       aths <- ruleCONJUNCTS #<< primASSUME atm
       rth <- foldr1M ruleCONJ #<< map2 rulePROVE_HYP aths ths
       eth <- proveRawRecursiveFunctionsExist ax atm
       let evs = fst . stripExists $ concl eth
       fth <- itlistM ruleSIMPLE_CHOOSE evs =<<
                foldrM ruleSIMPLE_EXISTS rth evs
       return $ rulePROVE_HYP eth fth


reshuffle :: HOLTerm -> [HOLTerm] -> [HOLThm] -> HOL cls thry [HOLThm]
reshuffle fn args acc =
    let args' = uncurry (flip (++)) $ partition isVar args in
      if args' == args then return acc
      else do gvs <- mapM (genVar . typeOf) args
              let gvs' = fromJust $ mapM (\ x -> x `lookup` zip args gvs) args'
              lty <- itlistM (mkFunTy . typeOf) gvs' <#<
                       funpowM (length gvs)
                         (liftM (head . tail . snd) . destType) $ typeOf fn
              fn' <- genVar lty
              def <- mkEq fn #<< listMkAbs gvs =<< listMkComb fn' gvs'
              def' <- fromRightM $ primASSUME def
              return (def':acc)
                         

proveRecursiveFunctionsExist :: BoolCtxt thry => HOLThm -> HOLTerm 
                             -> HOL cls thry HOLThm
proveRecursiveFunctionsExist ax tm =
    let rawcls = conjuncts tm
        spcls = map (snd . stripForall) rawcls
        lpats = fromJust $ mapM (liftM stripComb . lHand) spcls
        ufns = foldr (insert . fst) [] lpats
        uxargs = fromJust $ mapM (`lookup` lpats) ufns in
      do trths <- foldr2M reshuffle [] ufns uxargs
         pth <- thmBETA
         tth <- runConv (convGEN_REWRITE convREDEPTH (pth:trths)) tm
         eth <- proveCanonRecursiveFunctionsExist ax #<< rand (concl tth)
         let (evs, ebod) = stripExists $ concl eth
         stth <- fromRightM $ ruleSYM tth
         fth <- itlistM ruleSIMPLE_EXISTS ufns #<<
                  primEQ_MP stth #<< primASSUME ebod
         gth <- foldrM scrubDef fth $ map concl trths
         hth <- foldrM ruleSIMPLE_CHOOSE gth evs
         return $ rulePROVE_HYP eth hth
  where scrubDef :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
        scrubDef t th =
            do (l, r) <- liftMaybe "scrubDef: not an equation." $ destEq t
               th' <- ruleDISCH t th
               ruleMP (fromJust $ primINST [(l, r)] th') $ primREFL r


newRecursiveDefinition :: (NumsCtxt thry, 
                           HOLThmRep thm Theory thry,
                           HOLTermRep tm Theory thry) => String -> thm -> tm 
                       -> HOL Theory thry HOLThm
newRecursiveDefinition lbl pax ptm =
    (do acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty) 
        ths <- queryHOL acid GetDefinitions
        closeAcidStateHOL acid
        tm <- toHTm ptm
        th <- tryFind (findRedefinition tm) ths
        warn True "Benign redefinition of recursive function."
        return th)
    <|> do tm <- toHTm ptm
           let rawcls = conjuncts tm
               spcls = map (snd . stripForall) rawcls
           lpats <- liftMaybe ("newRecursiveDefinition: definition not " ++
                               "provided as a conjunction of equations.") $
                      mapM (liftM stripComb . lHand) spcls
           let ufns = foldr (insert . fst) [] lpats
               fvs = map (\ t -> frees t \\ ufns) rawcls
           gcls <- map2M listMkForall fvs rawcls
           ax <- toHThm pax
           eth <- proveRecursiveFunctionsExist ax =<< listMkConj gcls
           let (evs, _) = stripExists $ concl eth
           dth <- newSpecification (map (fst . fromJust . destVar) evs) eth
           dths <- map2M ruleSPECL fvs =<< ruleCONJUNCTS dth
           th <- foldr1M ruleCONJ dths
           acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty)
           updateHOL acid (InsertDefinition lbl th)
           createCheckpointAndCloseHOL acid
           return th
  where findRedefinition :: BoolCtxt thry => HOLTerm -> HOLThm 
                         -> HOL cls thry HOLThm
        findRedefinition tm th =
            do th' <- rulePART_MATCH return th tm
               _ <- rulePART_MATCH return th' $ concl th
               return th'
            
getRecursiveDefinition :: String -> HOL cls thry HOLThm
getRecursiveDefinition lbl =
    do acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty)
       qth <- queryHOL acid (GetADefinition lbl)
       closeAcidStateHOL acid
       liftMaybe ("getRecursiveDefinition: definition for " ++ lbl ++ 
                  " not found.") qth

