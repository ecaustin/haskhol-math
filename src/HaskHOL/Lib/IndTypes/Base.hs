{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, PatternSynonyms, QuasiQuotes, 
             ScopedTypeVariables, TemplateHaskell, TypeFamilies #-}
module HaskHOL.Lib.IndTypes.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)

import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypes.B
import HaskHOL.Lib.IndTypes.Pre

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef

--evnote: need list for distintness and injectivity stores because of dupe keys
{-# NOINLINE rectypeNet #-}
rectypeNet :: HOLRef (Maybe (Net (GConversion cls thry)))
rectypeNet = unsafePerformIO $ newIORef Nothing

data InductiveTypes = 
    InductiveTypes !(Map Text (HOLThm, HOLThm)) deriving Typeable

putInductiveTypes :: Map Text (HOLThm, HOLThm) -> Update InductiveTypes ()
putInductiveTypes m =
    put (InductiveTypes m)

getInductiveTypes :: Query InductiveTypes (Map Text (HOLThm, HOLThm))
getInductiveTypes =
    do (InductiveTypes m) <- ask
       return m

addInductiveType :: Text -> (HOLThm, HOLThm) -> Update InductiveTypes ()
addInductiveType s ths =
    do (InductiveTypes m) <- get
       put (InductiveTypes (mapInsert s ths m))

getInductiveType :: Text -> Query InductiveTypes (Maybe (HOLThm, HOLThm))
getInductiveType s =
    do (InductiveTypes m) <- ask
       return $! mapLookup s m

deriveSafeCopy 0 'base ''InductiveTypes

makeAcidic ''InductiveTypes 
  ['putInductiveTypes, 'getInductiveTypes, 'addInductiveType, 'getInductiveType]

data DistinctnessStore = 
    DistinctnessStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''DistinctnessStore

getDistinctnessStore :: Query DistinctnessStore [(Text, HOLThm)]
getDistinctnessStore = 
    do (DistinctnessStore m) <- ask
       return m

addDistinctnessStore :: Text -> [HOLThm] -> Update DistinctnessStore ()
addDistinctnessStore tyname ths =
    do (DistinctnessStore m) <- get
       put (DistinctnessStore (map (\ x -> (tyname, x)) ths ++ m))

putDistinctnessStore :: [(Text, HOLThm)] -> Update DistinctnessStore ()
putDistinctnessStore m =
    put (DistinctnessStore m)

makeAcidic ''DistinctnessStore 
    ['getDistinctnessStore, 'addDistinctnessStore, 'putDistinctnessStore]

data InjectivityStore = InjectivityStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''InjectivityStore

getInjectivityStore :: Query InjectivityStore [(Text, HOLThm)]
getInjectivityStore =
    do (InjectivityStore m) <- ask
       return m

addInjectivityStore :: Text -> [HOLThm] -> Update InjectivityStore ()
addInjectivityStore tyname ths =
    do (InjectivityStore m) <- get
       put (InjectivityStore (map (\ x -> (tyname, x)) ths ++ m))

makeAcidic ''InjectivityStore ['getInjectivityStore, 'addInjectivityStore]


rehashRectypeNet :: forall cls thry. BoolCtxt thry => HOL cls thry ()
rehashRectypeNet =
    do acid1 <- openLocalStateHOL (DistinctnessStore [])
       ths1 <- liftM (map snd) $ queryHOL acid1 GetDistinctnessStore
       closeAcidStateHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       ths2 <- liftM (map snd) $ queryHOL acid2 GetInjectivityStore
       closeAcidStateHOL acid2
       canonThl <- foldrM (mkRewrites False) [] $ ths1 ++ ths2
       net' <- liftO $ foldrM (netOfThm True) (netEmpty :: Net (GConversion cls thry)) canonThl
       writeHOLRef rectypeNet (Just net')

extendRectypeNet :: (BasicConvs thry, IndTypesBCtxt thry) 
                 => (Text, (Int, HOLThm, HOLThm)) 
                 -> HOL Theory thry ()
extendRectypeNet (tyname, (_, _, rth)) =
    do ths1 <- liftM (: []) (proveConstructorsDistinct rth) <|> return []
       ths2 <- liftM (:[]) (proveConstructorsInjective rth) <|> return []
       acid1 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid1 (AddDistinctnessStore tyname ths1)
       createCheckpointAndCloseHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       updateHOL acid2 (AddInjectivityStore tyname ths2)
       createCheckpointAndCloseHOL acid2
       rehashRectypeNet

basicRectypeNet :: BoolCtxt thry => HOL cls thry (Net (GConversion cls thry))
basicRectypeNet =
    do net <- readHOLRef rectypeNet
       case net of
         Just net' -> return net'
         Nothing -> do rehashRectypeNet
                       basicRectypeNet
             

indDefOption' :: (BasicConvs thry, IndTypesBCtxt thry) 
              => HOL Theory thry (HOLThm, HOLThm)
indDefOption' = defineTypeRaw =<< 
    parseInductiveTypeSpecification "option = NONE | SOME A"

indDefList' :: (BasicConvs thry, IndTypesBCtxt thry) 
            => HOL Theory thry (HOLThm, HOLThm)
indDefList' = defineTypeRaw =<< 
    parseInductiveTypeSpecification "list = NIL | CONS A list"

defISO' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defISO' = newDefinition "ISO"
    [str| ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\ (!y. g(f y) = y) |]

convUNWIND :: TheoremsCtxt thry => Conversion cls thry
convUNWIND = Conv $ \ tm ->
    let (evs, bod) = stripExists tm
        eqs = conjuncts bod in
      (do eq <- liftO $ find (\ x ->
                  case x of
                    (l := r) -> (l `elem` evs && not (l `freeIn` r)) ||
                                (r `elem` evs && not (r `freeIn` l))
                    _ -> False) eqs
          (l, r) <- liftO $ destEq eq
          let v = if l `elem` evs && not (l `freeIn` r) then l else r
              cjs' = eq : (eqs \\ [eq])
              n = length evs - (1 + fromJust (index v (reverse evs)))
          th1 <- ruleCONJ_ACI =<< mkEq bod =<< listMkConj cjs'
          th2 <- foldrM ruleMK_EXISTS th1 evs
          th3 <- runConv (funpow n convBINDER (convPUSH_EXISTS baseconv)) #<< 
                   rand (concl th2)
          ruleCONV (convRAND convUNWIND) #<< primTRANS th2 th3) <|>
      (return $! primREFL tm)
  where baseconv ::TheoremsCtxt thry => Conversion cls thry
        baseconv =
            convGEN_REWRITE id 
              [ thmUNWIND1, thmUNWIND2
              , ruleEQT_INTRO =<< ruleSPEC_ALL thmEXISTS_REFL
              , ruleEQT_INTRO =<< ruleGSYM (ruleSPEC_ALL thmEXISTS_REFL)
              ]

convINSIDE_EXISTS :: Conversion cls thry -> Conversion cls thry
convINSIDE_EXISTS conv = Conv $ \ tm ->
    if isExists tm then runConv (convBINDER (convINSIDE_EXISTS conv)) tm
    else runConv conv tm

convPUSH_EXISTS :: TheoremsCtxt thry => Conversion cls thry 
                -> Conversion cls thry
convPUSH_EXISTS bc = Conv $ \ tm -> 
    runConv (convREWR thmSWAP_EXISTS `_THEN` convBINDER (convPUSH_EXISTS bc)) tm
      <|> runConv bc tm
    
convBREAK_CONS :: TheoremsCtxt thry => Conversion cls thry
convBREAK_CONS = Conv $ \ tm ->
    do net <- basicRectypeNet
       let conv0 = convTOP_SWEEP (convREWRITES net)
           conv1 = if isConj tm then convLAND conv0 else conv0
       runConv (conv1 `_THEN` (convGEN_REWRITE convDEPTH 
                                 [ thmAND_CLAUSES, thmOR_CLAUSES ] `_THEN` 
                               convASSOC thmCONJ_ASSOC)) tm

convMATCH_SEQPATTERN_TRIV :: (BasicConvs thry, IndTypesBCtxt thry) 
                          => Conversion cls thry
convMATCH_SEQPATTERN_TRIV = 
    convMATCH_SEQPATTERN `_THEN` convGEN_REWRITE id [thmCOND_CLAUSES]

convMATCH_SEQPATTERN :: (BasicConvs thry, IndTypesBCtxt thry) 
                     => Conversion cls thry
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
  where convUNWIND_pth1 :: (BasicConvs thry, IndTypesBCtxt thry) 
                        => HOL cls thry HOLThm
        convUNWIND_pth1 = cacheProof "convUNWIND_pth1" ctxtIndTypesB $ prove
            [str| _MATCH x (_SEQPATTERN r s) =
                    (if ?y. r x y then _MATCH x r else _MATCH x s) /\
                  _FUNCTION (_SEQPATTERN r s) x =
                    (if ?y. r x y then _FUNCTION r x else _FUNCTION s x) |] $
              tacREWRITE [def_MATCH, def_SEQPATTERN, def_FUNCTION] `_THEN`
              tacMESON_NIL

        convUNWIND_pth2 :: (BasicConvs thry, IndTypesBCtxt thry) 
                        => HOL cls thry HOLThm
        convUNWIND_pth2 = cacheProof "convUNWIND_pth2" ctxtIndTypesB $ prove
          [str|((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> s = t) /\
               ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> s = t /\ p)|] $
            tacREWRITE [ def_UNGUARDED_PATTERN
                       , def_GUARDED_PATTERN, defGEQ ] `_THEN`
            tacMESON_NIL

convMATCH_ONEPATTERN_TRIV :: (BasicConvs thry, IndTypesBCtxt thry) 
                          => Conversion cls thry
convMATCH_ONEPATTERN_TRIV =
    convMATCH_ONEPATTERN `_THEN` convGEN_REWRITE id [convUNWIND_pth5]
  where convUNWIND_pth5 :: (BasicConvs thry, IndTypesBCtxt thry) 
                        => HOL cls thry HOLThm
        convUNWIND_pth5 = cacheProof "convUNWIND_pth5" ctxtIndTypesB $ 
            prove "(if ?!z. z = k then @z. z = k else @x. F) = k"
              tacMESON_NIL

convMATCH_ONEPATTERN :: (BasicConvs thry, IndTypesBCtxt thry) 
                     => Conversion cls thry
convMATCH_ONEPATTERN = Conv $ \ tm ->
    do th1 <- runConv (convGEN_REWRITE id [convUNWIND_pth3]) tm
       let tm' = fromJust $ body =<< rand =<< lHand =<< rand (concl th1)
       th2 <- runConv (convINSIDE_EXISTS
                       (convGEN_REWRITE id [convUNWIND_pth4] `_THEN`
                        convRAND convBREAK_CONS) `_THEN`
                       convUNWIND `_THEN`
                       convGEN_REWRITE convDEPTH
                       [ ruleEQT_INTRO =<< ruleSPEC_ALL thmEQ_REFL
                       , thmAND_CLAUSES
                       ] `_THEN`
                       convGEN_REWRITE convDEPTH [thmEXISTS_SIMP]) tm'
       let conv = Conv $ \ x -> if lHand (concl th2) == Just x
                                then return th2
                                else fail ""
       ruleCONV (convRAND 
                 (convRATOR 
                  (convCOMB2 (convRAND (convBINDER conv)) 
                   (convBINDER conv)))) th1
  where convUNWIND_pth3 :: (BasicConvs thry, IndTypesBCtxt thry) 
                        => HOL cls thry HOLThm
        convUNWIND_pth3 = cacheProof "convUNWIND_pth3" ctxtIndTypesB $ prove
          [str|(_MATCH x (\y z. P y z) = if ?!z. P x z then @z. P x z else @x. F) /\
               (_FUNCTION (\y z. P y z) x = if ?!z. P x z then @z. P x z else @x. F) |] $
            tacREWRITE [ def_MATCH, def_FUNCTION]

        convUNWIND_pth4 :: (BasicConvs thry, IndTypesBCtxt thry) 
                        => HOL cls thry HOLThm
        convUNWIND_pth4 = cacheProof "convUNWIND_pth4" ctxtIndTypesB $ prove
          [str|(_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> y = u /\ s = t) /\
           (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> y = u /\ s = t /\ p) |] $
              tacREWRITE [ def_UNGUARDED_PATTERN
                         , def_GUARDED_PATTERN, defGEQ ] `_THEN`
              tacMESON_NIL
