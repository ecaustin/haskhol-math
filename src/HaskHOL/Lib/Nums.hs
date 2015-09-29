{-|
  Module:    HaskHOL.Lib.Nums
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Nums
    ( NumsCtxt
    , ctxtNums
    , nums
    , defONE_ONE
    , defONTO
    , axINFINITY
    , thmIND_SUC_0_EXISTS
    , defIND_SUC
    , defIND_0
    , rulesNUM_REP
    , inductNUM_REP
    , casesNUM_REP
    , tyDefMkNum
    , tyDefDestNum
    , defZERO
    , defSUC
    , defNUMERAL
    , thmIND_SUC_SPEC
    , thmIND_SUC_INJ
    , thmIND_SUC_0
    , thmNOT_SUC_PRIM
    , thmSUC_INJ
    , thmNUM_ZERO_PRIM
    , inductionNUM_PRIM
    , thmNUM_AXIOM_PRIM
    , thmNOT_SUC
    , inductionNUM
    , thmNUM_AXIOM
    , recursionNUM
    , recursionStdNUM
    , defBIT0_PRIM
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

import qualified HaskHOL.Lib.Nums.Base as Base
import HaskHOL.Lib.Nums.Context
import HaskHOL.Lib.Nums.PQ

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition, newSpecification,
                                 getSpecification)
import HaskHOL.Lib.Pair

-- Stage 1
defONE_ONE :: NumsCtxt thry => HOL cls thry HOLThm
defONE_ONE = cacheProof "defONE_ONE" ctxtNums $ getDefinition "ONE_ONE"

defONTO :: NumsCtxt thry => HOL cls thry HOLThm
defONTO = cacheProof "defONTO" ctxtNums $ getDefinition "ONTO"

axINFINITY :: NumsCtxt thry => HOL cls thry HOLThm
axINFINITY = cacheProof "axINFINITY" ctxtNums $ getAxiom "axINFINITY"

-- Stage 2
defIND_SUC :: NumsCtxt thry => HOL cls thry HOLThm
defIND_SUC = cacheProof "defIND_SUC" ctxtNums $ getDefinition "IND_SUC"

defIND_0 :: NumsCtxt thry => HOL cls thry HOLThm
defIND_0 = cacheProof "defIND_0" ctxtNums $ getDefinition "IND_0"

defZERO :: NumsCtxt thry => HOL cls thry HOLThm
defZERO = cacheProof "defZERO" ctxtNums $ getDefinition "_0"

defSUC :: NumsCtxt thry => HOL cls thry HOLThm
defSUC = cacheProof "defSUC" ctxtNums $ getDefinition "SUC"

defNUMERAL :: NumsCtxt thry => HOL cls thry HOLThm
defNUMERAL = cacheProof "defNUMERAL" ctxtNums $ getDefinition "NUMERAL"

rulesNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
rulesNUM_REP = cacheProof "rulesNUM_REP" ctxtNums Base.rulesNUM_REP

inductNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
inductNUM_REP = cacheProof "inductNUM_REP" ctxtNums Base.inductNUM_REP

casesNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
casesNUM_REP = cacheProof "casesNUM_REP" ctxtNums $
    do (_, _, th) <- getInductiveDefinition "NUM_REP"
       return th

tyDefMkNum :: NumsCtxt thry => HOL cls thry HOLThm
tyDefMkNum = cacheProof "tyDefMkNum" ctxtNums Base.tyDefMkNum

tyDefDestNum :: NumsCtxt thry => HOL cls thry HOLThm
tyDefDestNum = cacheProof "tyDefDestNum" ctxtNums Base.tyDefDestNum

-- Stage 3
defBIT0_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
defBIT0_PRIM = cacheProof "defBIT0_PRIM" ctxtNums $ getDefinition "BIT0"

defBIT1 :: NumsCtxt thry => HOL cls thry HOLThm
defBIT1 = cacheProof "defBIT1" ctxtNums $ getDefinition "BIT1"

pattern ZERO <- Const "_0" _
pattern SUC <- Const "SUC" _
pattern NUMERAL tm <- Comb (Const "NUMERAL" _) tm
pattern BIT0 tm <- Comb (Const "BIT0" _) tm
pattern BIT1 tm <- Comb (Const "BIT1" _) tm

thmIND_SUC_0_EXISTS :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0_EXISTS = 
    cacheProof "thmIND_SUC_0_EXISTS" ctxtNums Base.thmIND_SUC_0_EXISTS

thmIND_SUC_SPEC :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_SPEC = cacheProof "thmIND_SUC_SPEC" ctxtNums Base.thmIND_SUC_SPEC

thmIND_SUC_INJ :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_INJ = cacheProof "thmIND_SUC_INJ" ctxtNums Base.thmIND_SUC_INJ

thmIND_SUC_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0 = cacheProof "thmIND_SUC_0" ctxtNums Base.thmIND_SUC_0

thmNUM_ZERO_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_ZERO_PRIM = cacheProof "thmNUM_ZERO_PRIM" ctxtNums Base.thmNUM_ZERO_PRIM

thmNOT_SUC_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_SUC_PRIM = cacheProof "thmNOT_SUC'" ctxtNums Base.thmNOT_SUC_PRIM

thmNOT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_SUC = cacheProof "thmNOT_SUC" ctxtNums Base.thmNOT_SUC

thmSUC_INJ :: NumsCtxt thry => HOL cls thry HOLThm
thmSUC_INJ = cacheProof "thmSUC_INJ" ctxtNums Base.thmSUC_INJ

inductionNUM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
inductionNUM_PRIM = 
    cacheProof "inductionNUM_PRIM" ctxtNums Base.inductionNUM_PRIM

inductionNUM :: NumsCtxt thry => HOL cls thry HOLThm
inductionNUM = cacheProof "inductionNUM" ctxtNums Base.inductionNUM

thmNUM_AXIOM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM_PRIM = cacheProof "thmNUM_AXIOM'" ctxtNums Base.thmNUM_AXIOM_PRIM

thmNUM_AXIOM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM = cacheProof "thmNUM_AXIOM" ctxtNums Base.thmNUM_AXIOM

recursionNUM :: NumsCtxt thry => HOL cls thry HOLThm
recursionNUM = cacheProof "recursionNUM" ctxtNums Base.recursionNUM

recursionStdNUM :: NumsCtxt thry => HOL cls thry HOLThm
recursionStdNUM = cacheProof "recursionStdNUM" ctxtNums Base.recursionStdNUM

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


defBIT0 :: NumsCtxt thry => HOL cls thry HOLThm
defBIT0 = cacheProof "defBIT0" ctxtNums $
    do th <- ruleBETA =<< 
               ruleISPECL ["0", "\\m n:num. SUC (SUC m)"] recursionNUM
       ruleREWRITE [ruleGSYM defBIT0_PRIM] =<< ruleSELECT th

tacINDUCT :: NumsCtxt thry => Tactic cls thry
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

newSpecification :: NumsCtxt thry => [Text] -> HOLThm -> HOL Theory thry HOLThm
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
  where specifies :: NumsCtxt thry => [Text] -> HOLThm -> HOL Theory thry HOLThm
        specifies [] thm = return thm
        specifies (n:ns) thm =
            do th' <- specify n thm
               specifies ns th'

        specify :: NumsCtxt thry => Text -> HOLThm -> HOL Theory thry HOLThm
        specify name thm =
            do ntm <- mkCode $ unpack name
               gv <- genVar $ typeOf ntm
               th0 <- ruleCONV (convREWR thmSKOLEM) =<< ruleGEN gv thm
               th1 <- ruleCONV (convRATOR (convREWR thmEXISTS) `_THEN` 
                                convBETA) th0
               let (_, r) = fromJust . destComb $ concl th1
                   rn = fromRight $ mkComb r ntm
               tm <- mkEq (mkVar name $ typeOf rn) rn
               th2 <- newDefinition (name, tm)
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
               
