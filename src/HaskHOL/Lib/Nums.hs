{-# LANGUAGE PatternSynonyms, QuasiQuotes #-}
{-|
  Module:    HaskHOL.Lib.Nums
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Nums
    ( NumsType
    , NumsCtxt
    , defONE_ONE -- A
    , defONTO
    , axINFINITY -- B
    , thmIND_SUC_0_EXISTS
    , defIND_SUC -- C
    , defIND_0
    , rulesNUM_REP
    , inductNUM_REP
    , casesNUM_REP
    , tyDefMkNum
    , tyDefDestNum
    , defZERO
    , defSUC
    , defNUMERAL
    , thmIND_SUC_SPEC -- Stage2
    , thmIND_SUC_INJ -- Stage 3
    , thmIND_SUC_0
    , thmNOT_SUC' --Stage4
    , thmSUC_INJ
    , inductionNUM' -- Stage5
    , thmNUM_AXIOM' -- Stage6
    , thmNOT_SUC  -- Stage7
    , inductionNUM
    , thmNUM_AXIOM
    , recursionNUM -- Stage 8
    , recursionStdNUM -- Base
    , defBIT0'
    , defBIT1
    , tacINDUCT
    , mkNumeral
    , mkSmallNumeral
    , destSmallNumeral
    , isNumeral
    , newSpecification
    , getSpecification
    , ruleDENUMERAL
    , defBIT0
    , pattern ZERO
    , pattern SUC
    , pattern NUMERAL
    , pattern BIT0
    , pattern BIT1
    ) where

import HaskHOL.Lib.Nums.B
import HaskHOL.Lib.Nums.Base
import HaskHOL.Lib.Nums.Context

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition, newSpecification,
                                 getSpecification)
import HaskHOL.Lib.Pair

defBIT0' :: NumsCtxt thry => HOL cls thry HOLThm
defBIT0' = cacheProof "defBIT0'" ctxtNums $ getDefinition "BIT0"

defBIT1 :: NumsCtxt thry => HOL cls thry HOLThm
defBIT1 = cacheProof "defBIT1" ctxtNums $ getDefinition "BIT1"

pattern ZERO <- Const "_0" _
pattern SUC <- Const "SUC" _
pattern NUMERAL tm <- Comb (Const "NUMERAL" _) tm
pattern BIT0 tm <- Comb (Const "BIT0" _) tm
pattern BIT1 tm <- Comb (Const "BIT1" _) tm

data TheSpecifications = 
    TheSpecifications ![(([Text], HOLThm), HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''TheSpecifications

getSpecifications :: Query TheSpecifications [(([Text], HOLThm), HOLThm)]
getSpecifications =
    do (TheSpecifications specs) <- ask
       return specs

getASpecification :: [Text] -> Query TheSpecifications (Maybe HOLThm)
getASpecification names =
    do (TheSpecifications specs) <- ask
       case find (\ ((names', _), _) -> names' == names) specs of
         Just (_, th) -> return $! Just th
         Nothing -> return Nothing

addSpecification :: [Text] -> HOLThm -> HOLThm -> Update TheSpecifications ()
addSpecification names th sth =
    do (TheSpecifications specs) <- get
       put (TheSpecifications (((names, th), sth) : specs))

makeAcidic ''TheSpecifications 
    ['getSpecifications, 'getASpecification, 'addSpecification]


defBIT0 :: (BasicConvs thry, NumsCtxt thry) => HOL cls thry HOLThm
defBIT0 = cacheProof "defBIT0" ctxtNums $
    do th <- ruleBETA =<< 
               ruleISPECL ["0", "\\m n:num. SUC (SUC m)"] recursionNUM
       ruleREWRITE [ruleGSYM defBIT0'] =<< ruleSELECT th

tacINDUCT :: (BasicConvs thry, NumsCtxt thry) => Tactic cls thry
tacINDUCT = tacMATCH_MP inductionNUM `_THEN` tacCONJ `_THENL` 
            [_ALL, tacGEN `_THEN` tacDISCH]

mkNumeral :: (Integral i, NumsCtxt thry) => i -> HOL cls thry HOLTerm
mkNumeral n
    | n < 0 = fail "mkNumeral: negative argument"
    | otherwise = 
          do numeral <- serve [nums| NUMERAL |]
             n' <- mkNum n
             liftO $ mkComb numeral n'
  where mkNum :: (Integral i, NumsCtxt thry) => i -> HOL cls thry HOLTerm
        mkNum x
            | x == 0 = serve [nums| _0 |]
            | otherwise =
                do l <- if x `mod` 2 == 0 then serve [nums| BIT0 |]
                        else serve [nums| BIT1 |]
                   r <- mkNum $ x `div` 2
                   liftO $ mkComb l r

mkSmallNumeral :: NumsCtxt thry => Int -> HOL cls thry HOLTerm
mkSmallNumeral = mkNumeral

destSmallNumeral :: HOLTerm -> Maybe Int
destSmallNumeral = liftM fromInteger . destNumeral

isNumeral :: HOLTerm -> Bool
isNumeral = isJust . destNumeral

newSpecification :: (BasicConvs thry, NumsCtxt thry) => [Text] -> HOLThm 
                 -> HOL Theory thry HOLThm
newSpecification [] _ = fail "newSpecification: no constant names provided."
newSpecification names th@(Thm asl c)
    | not $ null asl = fail $ "newSpecification: " ++ 
                             "assumptions not allowed in theorem."
    | not . null $ frees c = fail $ "newSpecification: " ++
                                    "free variables in predicate."
    | otherwise =
        let (avs, _) = stripExists c 
            ns = length names in
          do failWhen (return $ ns > length avs) $
               "newSpecification: too many constant names provided."
             failWhen (return $ (length $ nub names) /= ns) $
               "newSpecification: constant names not distinct"
             acid <- openLocalStateHOL (TheSpecifications [])
             specs <- queryHOL acid GetSpecifications
             closeAcidStateHOL acid
             case find (\ ((names', th'), _) ->
                        names' == names && c `aConv` concl th') specs of
               Just (_, sth) -> 
                   do warn True "newSpecification: benign respecification."
                      return sth
               _ -> do sth <- specifies names th
                       acid' <- openLocalStateHOL (TheSpecifications [])
                       updateHOL acid' (AddSpecification names th sth)
                       createCheckpointAndCloseHOL acid'
                       return sth
  where specifies :: (BasicConvs thry, NumsCtxt thry) => [Text] -> HOLThm 
                  -> HOL Theory thry HOLThm
        specifies [] thm = return thm
        specifies (n:ns) thm =
            do th' <- specify n thm
               specifies ns th'

        specify :: (BasicConvs thry, NumsCtxt thry) => Text -> HOLThm 
                -> HOL Theory thry HOLThm
        specify name thm =
            do ntm <- mkCode $ unpack name
               gv <- genVar $ typeOf ntm
               th0 <- ruleCONV (convREWR thmSKOLEM) =<< ruleGEN gv thm
               th1 <- ruleCONV (convRATOR (convREWR thmEXISTS) `_THEN` 
                                convBETA) th0
               let (_, r) = fromJust . destComb $ concl th1
                   rn = fromRight $ mkComb r ntm
               tm <- mkEq (mkVar name $ typeOf rn) rn
               th2 <- newDefinition name tm
               th3 <- ruleGSYM th2
               ruleGEN_REWRITE convONCE_DEPTH [th3] =<< ruleSPEC ntm =<< 
                 ruleCONV convBETA th1

        mkCode :: NumsCtxt thry => String -> HOL cls thry HOLTerm
        mkCode name = 
            foldr1M mkPair =<< mapM (mkNumeral . fromEnum) name
newSpecification _ _ = fail "newSpecification: exhausting warning."

getSpecification :: [Text] -> HOL cls thry HOLThm
getSpecification names =
    do acid <- openLocalStateHOL (TheSpecifications [])
       th <- queryHOL acid (GetASpecification names)
       closeAcidStateHOL acid
       liftMaybe "getSpecification: constants not found." th

ruleDENUMERAL :: (NumsCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry HOLThm
ruleDENUMERAL = ruleGEN_REWRITE convDEPTH [defNUMERAL] <=< toHThm
               
