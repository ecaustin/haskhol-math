{-# LANGUAGE FlexibleContexts #-}
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
    TheRecursiveDefinitions !(Map Text HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''TheRecursiveDefinitions

insertDefinition :: Text -> HOLThm -> Update TheRecursiveDefinitions ()
insertDefinition lbl thm =
    do TheRecursiveDefinitions defs <- get
       put (TheRecursiveDefinitions (mapInsert lbl thm defs))

getDefinitions :: Query TheRecursiveDefinitions [HOLThm]
getDefinitions =
    do TheRecursiveDefinitions defs <- ask
       return $! mapElems defs

getADefinition :: Text -> Query TheRecursiveDefinitions (Maybe HOLThm)
getADefinition name =
    do (TheRecursiveDefinitions defs) <- ask
       return $! name `mapAssoc` defs

makeAcidic ''TheRecursiveDefinitions 
    ['insertDefinition, 'getDefinitions, 'getADefinition]


proveRawRecursiveFunctionsExist :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                                => thm -> HOLTerm -> HOL cls thry HOLThm
proveRawRecursiveFunctionsExist ax tm =
    let rawcls = conjuncts tm
        spcls = map (snd . stripForall) rawcls in
      do lpats <- mapM (liftM stripComb . lHand) spcls
         let ufns = foldr (insert . fst) [] lpats
         axth <- ruleSPEC_ALL ax
         let (exvs, axbody) = stripExists $ concl axth
             axcls = conjuncts axbody
             f = liftM fst . (destConst <=< repeatM rator <=< rand <=<
                              lHand . snd . stripForall)
             findax (x, _) = assoc x =<< mapM (\ t -> do f' <- f t
                                                         return (f', t)) axcls
         raxs <- mapM (findax <=< destConst <=< repeatM rator . head . snd) 
                   lpats
         axfns <- mapM (repeatM rator <=< lHand . snd . stripForall) raxs
         let urfns =  map (\ v -> 
                        assocd v (setify . zip axfns $ map fst lpats) v) exvs
         axtm <- listMkExists exvs =<< listMkConj raxs
         urtm <- listMkExists urfns tm
         insts <- termMatch [] axtm urtm
         ixth <- ruleINSTANTIATE insts axth
         let (ixvs, ixbody) = stripExists $ concl ixth
         ixtm <- subst (zip ixvs urfns) ixbody
         ixths <- ruleCONJUNCTS $ primASSUME ixtm
         rixths <- mapM (\ t -> find (aConv t . concl) ixths) rawcls
         rixth <- itlistM ruleSIMPLE_EXISTS ufns =<< foldr1M ruleCONJ rixths
         rixth' <- foldrM ruleSIMPLE_CHOOSE rixth urfns
         rulePROVE_HYP ixth rixth'
                   

canonize :: BoolCtxt thry => HOLTerm -> HOL cls thry HOLThm
canonize t =
    let (avs, bod) = stripForall t in
      do (l, r) <- destEq bod
         let (fn, rarg:vargs) = stripComb l
         l' <- mkComb fn rarg
         r' <- listMkAbs vargs r
         let fvs = frees rarg
         t' <- listMkForall fvs =<< mkEq l' r'
         ruleGENL avs . ruleRIGHT_BETAS vargs . ruleSPECL fvs $ primASSUME t'
         

proveCanonRecursiveFunctionsExist :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                                  => thm -> HOLTerm -> HOL cls thry HOLThm
proveCanonRecursiveFunctionsExist ax tm =
    do ths <- mapM canonize $ conjuncts tm
       atm <- listMkConj $ map (head . hyp) ths
       aths <- ruleCONJUNCTS $ primASSUME atm
       rth <- foldr1M ruleCONJ =<< map2M rulePROVE_HYP aths ths
       eth <- proveRawRecursiveFunctionsExist ax atm
       let evs = fst . stripExists $ concl eth
       fth <- itlistM ruleSIMPLE_CHOOSE evs =<<
                foldrM ruleSIMPLE_EXISTS rth evs
       rulePROVE_HYP eth fth


reshuffle :: HOLTerm -> [HOLTerm] -> [HOLThm] -> HOL cls thry [HOLThm]
reshuffle fn args acc =
    let args' = uncurry (flip (++)) $ partition isVar args in
      if args' == args then return acc
      else do gvs <- mapM (genVar . typeOf) args
              gvs' <- mapM (\ x -> x `assoc` zip args gvs) args'
              lty <- itlistM (mkFunTy . typeOf) gvs' =<<
                       funpowM (length gvs)
                         (liftM (head . tail . snd) . destType) =<< typeOf fn
              fn' <- genVar lty
              def <- mkEq fn =<< listMkAbs gvs =<< listMkComb fn' gvs'
              def' <- primASSUME def
              return (def':acc)
                         

proveRecursiveFunctionsExist :: (BoolCtxt thry, HOLThmRep thm cls thry) 
                             => thm -> HOLTerm -> HOL cls thry HOLThm
proveRecursiveFunctionsExist ax tm =
    let rawcls = conjuncts tm
        spcls = map (snd . stripForall) rawcls in
      do lpats <- mapM (liftM stripComb . lHand) spcls
         let ufns = foldr (insert . fst) [] lpats
         uxargs <- mapM (`assoc` lpats) ufns
         trths <- foldr2M reshuffle [] ufns uxargs
         pth <- thmBETA
         tth <- runConv (convGEN_REWRITE convREDEPTH (pth:trths)) tm
         eth <- proveCanonRecursiveFunctionsExist ax =<< rand (concl tth)
         let (evs, ebod) = stripExists $ concl eth
         stth <- ruleSYM tth
         fth <- itlistM ruleSIMPLE_EXISTS ufns =<<
                  primEQ_MP stth (primASSUME ebod)
         gth <- foldrM scrubDef fth $ map concl trths
         hth <- foldrM ruleSIMPLE_CHOOSE gth evs
         rulePROVE_HYP eth hth
  where scrubDef :: BoolCtxt thry => HOLTerm -> HOLThm -> HOL cls thry HOLThm
        scrubDef t th =
            do (l, r) <- destEq t
               th' <- ruleDISCH t th
               ruleMP (primINST [(l, r)] th') $ primREFL r


newRecursiveDefinition :: (NumsCtxt thry, 
                           HOLThmRep thm Theory thry,
                           HOLTermRep tm Theory thry) => thm -> (Text, tm)
                       -> HOL Theory thry HOLThm
newRecursiveDefinition pax (lbl, ptm) =
    (do acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty) 
        ths <- queryHOL acid GetDefinitions
        closeAcidStateHOL acid
        th <- tryFind (findRedefinition ptm) ths
        warn True "Benign redefinition of recursive function."
        return th)
    <|> do tm <- toHTm ptm
           let rawcls = conjuncts tm
               spcls = map (snd . stripForall) rawcls
           lpats <- mapM (liftM stripComb . lHand) spcls
           let ufns = foldr (insert . fst) [] lpats
               fvs = map (\ t -> frees t \\ ufns) rawcls
           gcls <- map2M listMkForall fvs rawcls
           eth <- proveRecursiveFunctionsExist pax =<< listMkConj gcls
           let (evs, _) = stripExists $ concl eth
           evs' <- mapM (liftM fst . destVar) evs
           dth <- newSpecification evs' eth
           dths <- map2M ruleSPECL fvs =<< ruleCONJUNCTS dth
           th <- foldr1M ruleCONJ dths
           acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty)
           updateHOL acid (InsertDefinition lbl th)
           closeAcidStateHOL acid
           return th
  where findRedefinition :: (BoolCtxt thry, HOLTermRep tm cls thry) 
                         => tm -> HOLThm -> HOL cls thry HOLThm
        findRedefinition tm th =
            do th' <- rulePART_MATCH return th tm
               _ <- rulePART_MATCH return th' $ concl th
               return th'
            
getRecursiveDefinition :: Text -> HOL cls thry HOLThm
getRecursiveDefinition lbl =
    do acid <- openLocalStateHOL (TheRecursiveDefinitions mapEmpty)
       qth <- queryHOL acid (GetADefinition lbl)
       closeAcidStateHOL acid
       case qth of
         Just res -> return res
         _ -> fail $ "getRecursiveDefinition: definition for " ++ unpack lbl ++ 
                     " not found."

