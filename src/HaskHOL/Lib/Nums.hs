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

axINFINITY :: NumsCtxt thry => HOL cls thry HOLThm
axINFINITY = Base.axINFINITY

defONE_ONE :: NumsCtxt thry => HOL cls thry HOLThm
defONE_ONE = Base.defONE_ONE

defONTO :: NumsCtxt thry => HOL cls thry HOLThm
defONTO = Base.defONTO

defIND_SUC :: NumsCtxt thry => HOL cls thry HOLThm
defIND_SUC = Base.defIND_SUC

defIND_0 :: NumsCtxt thry => HOL cls thry HOLThm
defIND_0 = Base.defIND_0

defZERO :: NumsCtxt thry => HOL cls thry HOLThm
defZERO = Base.defZERO

defSUC :: NumsCtxt thry => HOL cls thry HOLThm
defSUC = Base.defSUC

defNUMERAL :: NumsCtxt thry => HOL cls thry HOLThm
defNUMERAL = Base.defNUMERAL

rulesNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
rulesNUM_REP = Base.rulesNUM_REP

inductNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
inductNUM_REP = Base.inductNUM_REP

casesNUM_REP :: NumsCtxt thry => HOL cls thry HOLThm
casesNUM_REP = cacheProof "casesNUM_REP" ctxtNums $
    do (_, _, th) <- getInductiveDefinition "NUM_REP"
       return th

tyDefMkNum :: NumsCtxt thry => HOL cls thry HOLThm
tyDefMkNum = Base.tyDefMkNum

tyDefDestNum :: NumsCtxt thry => HOL cls thry HOLThm
tyDefDestNum = Base.tyDefDestNum

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
thmIND_SUC_0_EXISTS = Base.thmIND_SUC_0_EXISTS

thmIND_SUC_SPEC :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_SPEC = Base.thmIND_SUC_SPEC

thmIND_SUC_INJ :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_INJ = Base.thmIND_SUC_INJ

thmIND_SUC_0 :: NumsCtxt thry => HOL cls thry HOLThm
thmIND_SUC_0 = Base.thmIND_SUC_0

thmNUM_ZERO_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_ZERO_PRIM = Base.thmNUM_ZERO_PRIM

thmNOT_SUC_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_SUC_PRIM = Base.thmNOT_SUC_PRIM

thmNOT_SUC :: NumsCtxt thry => HOL cls thry HOLThm
thmNOT_SUC = Base.thmNOT_SUC

thmSUC_INJ :: NumsCtxt thry => HOL cls thry HOLThm
thmSUC_INJ = Base.thmSUC_INJ

inductionNUM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
inductionNUM_PRIM = Base.inductionNUM_PRIM

inductionNUM :: NumsCtxt thry => HOL cls thry HOLThm
inductionNUM = Base.inductionNUM

thmNUM_AXIOM_PRIM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM_PRIM = Base.thmNUM_AXIOM_PRIM

thmNUM_AXIOM :: NumsCtxt thry => HOL cls thry HOLThm
thmNUM_AXIOM = Base.thmNUM_AXIOM

recursionNUM :: NumsCtxt thry => HOL cls thry HOLThm
recursionNUM = Base.recursionNUM

recursionStdNUM :: NumsCtxt thry => HOL cls thry HOLThm
recursionStdNUM = Base.recursionStdNUM

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
    do th <- ruleBETA $ 
               ruleISPECL [[txt| 0 |], [txt| \m n:num. SUC (SUC m) |]] 
                 recursionNUM
       ruleREWRITE [ruleGSYM defBIT0_PRIM] $ ruleSELECT th

tacINDUCT :: NumsCtxt thry => Tactic cls thry
tacINDUCT = tacMATCH_MP inductionNUM `_THEN` tacCONJ `_THENL` 
            [_ALL, tacGEN `_THEN` tacDISCH]

mkNumeral :: (Integral i, NumsCtxt thry) => i -> HOL cls thry HOLTerm
mkNumeral n
    | n < 0 = fail "mkNumeral: negative argument"
    | otherwise = mkComb (serve [nums| NUMERAL |]) $ mkNum n
  where mkNum :: (Integral i, NumsCtxt thry) => i -> HOL cls thry HOLTerm
        mkNum x
            | x == 0 = serve [nums| _0 |]
            | otherwise =
                do l <- if x `mod` 2 == 0 then serve [nums| BIT0 |]
                        else serve [nums| BIT1 |]
                   r <- mkNum $ x `div` 2
                   mkComb l r

mkSmallNumeral :: NumsCtxt thry => Int -> HOL cls thry HOLTerm
mkSmallNumeral = mkNumeral

destSmallNumeral :: HOLTerm -> Maybe Int
destSmallNumeral = liftM fromInteger . destNumeral

isNumeral :: HOLTerm -> Bool
isNumeral = try' . can destNumeral

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
                       closeAcidStateHOL acid'
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
               th0 <- ruleCONV (convREWR thmSKOLEM) $ ruleGEN gv thm
               th1 <- ruleCONV (convRATOR (convREWR thmEXISTS) `_THEN` 
                                convBETA) th0
               (_, r) <- destComb $ concl th1
               rn <- mkComb r ntm
               tm <- mkEq (mkVar name $ typeOf rn) rn
               th2 <- newDefinition (name, tm)
               th3 <- ruleGSYM th2
               ruleGEN_REWRITE convONCE_DEPTH [th3] . ruleSPEC ntm $ 
                 ruleCONV convBETA th1

        mkCode :: NumsCtxt thry => String -> HOL cls thry HOLTerm
        mkCode name = 
            foldr1M mkPair =<< mapM (mkNumeral . fromEnum) name
newSpecification _ _ = fail "newSpecification: exhausting warning."

getSpecification :: [Text] -> HOL cls thry HOLThm
getSpecification names =
    do acid <- openLocalStateHOL (TheSpecifications [])
       qth <- queryHOL acid (GetASpecification names)
       closeAcidStateHOL acid
       case qth of
         Just res -> return res
         _ -> fail "getSpecification: constants not found."

ruleDENUMERAL :: (NumsCtxt thry, HOLThmRep thm cls thry) => thm 
              -> HOL cls thry HOLThm
ruleDENUMERAL = ruleGEN_REWRITE convDEPTH [defNUMERAL] <=< toHThm
               
