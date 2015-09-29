{-# LANGUAGE FlexibleContexts #-}
module HaskHOL.Lib.Pair
    ( PairCtxt
    , ctxtPair
    , pair
    , defLET
    , defLET_END
    , defGABS
    , defGEQ
    , def_SEQPATTERN
    , def_UNGUARDED_PATTERN
    , def_GUARDED_PATTERN
    , def_MATCH
    , def_FUNCTION
    , defMK_PAIR
    , thmPAIR_EXISTS
    , tyDefProd
    , defCOMMA
    , defFST
    , defSND
    , thmREP_ABS_PAIR
    , thmPAIR_SURJECTIVE
    , thmPAIR_EQ
    , thmFST
    , thmSND
    , thmPAIR
    , recursionPAIR
    , inductPAIR
    , defCURRY
    , defUNCURRY
    , defPASSOC
    , convGEN_BETA
    , mkPair
    , destPair
    , newDefinition
    , getDefinition
    , thmFORALL_PAIR
    , createIteratedProjections
    , createProjections
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition, getDefinition)

import qualified HaskHOL.Lib.Pair.Base as Base
import HaskHOL.Lib.Pair.Context
import HaskHOL.Lib.Pair.PQ

-- Definition mechanics
newDefinition :: (PairCtxt thry, HOLTermRep tm Theory thry) 
              => (Text, tm) -> HOL Theory thry HOLThm
newDefinition = Base.newDefinition (thmFST, thmSND)

getDefinition :: Text -> HOL cls thry HOLThm
getDefinition lbl =
    do acid <- openLocalStateHOL (Base.Definitions mapEmpty)
       qth <- queryHOL acid (Base.GetDefinitionPrim lbl)
       closeAcidStateHOL acid
       liftMaybe ("getDefinition: definition for " ++ show lbl ++ 
                  " not found.") qth


-- Definitions
defLET :: PairCtxt thry => HOL cls thry HOLThm
defLET = cacheProof "defLET" ctxtPair $ getDefinition "LET"

defLET_END :: PairCtxt thry => HOL cls thry HOLThm
defLET_END = cacheProof "defLET_END" ctxtPair $ getDefinition "LET_END"

defGABS :: PairCtxt thry => HOL cls thry HOLThm
defGABS = cacheProof "defGABS" ctxtPair $ getDefinition "GABS"

defGEQ :: PairCtxt thry => HOL cls thry HOLThm
defGEQ = cacheProof "defGEQ" ctxtPair $ getDefinition "GEQ"

def_SEQPATTERN :: PairCtxt thry => HOL cls thry HOLThm
def_SEQPATTERN = cacheProof "def_SEQPATTERN" ctxtPair $ 
    getDefinition "_SEQPATTERN"

def_UNGUARDED_PATTERN :: PairCtxt thry => HOL cls thry HOLThm
def_UNGUARDED_PATTERN = cacheProof "def_UNGUARDED_PATTERN" ctxtPair $
    getDefinition "_UNGUARDED_PATTERN"

def_GUARDED_PATTERN :: PairCtxt thry => HOL cls thry HOLThm
def_GUARDED_PATTERN = cacheProof "def_GUARDED_PATTERN" ctxtPair $ 
    getDefinition "_GUARDED_PATTERN"

def_MATCH :: PairCtxt thry => HOL cls thry HOLThm
def_MATCH = cacheProof "def_MATCH" ctxtPair $ getDefinition "_MATCH"

def_FUNCTION :: PairCtxt thry => HOL cls thry HOLThm
def_FUNCTION = cacheProof "def_FUNCTION" ctxtPair $ getDefinition "_FUNCTION"

defMK_PAIR :: PairCtxt thry => HOL cls thry HOLThm
defMK_PAIR = cacheProof "defMK_PAIR" ctxtPair $ getDefinition "mk_pair"

defCOMMA :: PairCtxt thry => HOL cls thry HOLThm
defCOMMA = cacheProof "defCOMMA" ctxtPair $ getDefinition ","

defFST :: PairCtxt thry => HOL cls thry HOLThm
defFST = cacheProof "defFST" ctxtPair $ getDefinition "FST"

defSND :: PairCtxt thry => HOL cls thry HOLThm
defSND = cacheProof "defSND" ctxtPair $ getDefinition "SND"

defCURRY :: PairCtxt thry => HOL cls thry HOLThm
defCURRY = cacheProof "defCURRY" ctxtPair $ getDefinition "CURRY"

defUNCURRY :: PairCtxt thry => HOL cls thry HOLThm
defUNCURRY = cacheProof "defUNCURRY" ctxtPair $ getDefinition "UNCURRY"

defPASSOC :: PairCtxt thry => HOL cls thry HOLThm
defPASSOC = cacheProof "defPASSOC" ctxtPair $ getDefinition "PASSOC"

tyDefProd :: PairCtxt thry => HOL cls thry HOLThm
tyDefProd = cacheProof "tyDefProd" ctxtPair $ getTypeDefinition "prod"

-- syntax
mkPair :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkPair = mkBinary ","

destPair :: HOLTerm -> Maybe (HOLTerm, HOLTerm)
destPair = destBinary ","

-- theorems
thmPAIR_EXISTS :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_EXISTS = cacheProof "thmPAIR_EXISTS" ctxtPair Base.thmPAIR_EXISTS

thmFORALL_PAIR :: PairCtxt thry => HOL cls thry HOLThm
thmFORALL_PAIR = cacheProof "thmFORALL_PAIR" ctxtPair $
    prove "!P. (!p. P p) <=> (!p1 p2. P(p1,p2))" $
      tacMESON [thmPAIR]

thmREP_ABS_PAIR :: PairCtxt thry => HOL cls thry HOLThm
thmREP_ABS_PAIR = cacheProof "thmREP_ABS_PAIR" ctxtPair Base.thmREP_ABS_PAIR

thmPAIR_SURJECTIVE :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_SURJECTIVE = 
    cacheProof "thmPAIR_SURJECTIVE" ctxtPair Base.thmPAIR_SURJECTIVE

thmPAIR_EQ :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_EQ = cacheProof "thmPAIR_EQ" ctxtPair Base.thmPAIR_EQ

thmFST :: PairCtxt thry => HOL cls thry HOLThm
thmFST = cacheProof "thmFST" ctxtPair Base.thmFST

thmSND :: PairCtxt thry => HOL cls thry HOLThm
thmSND = cacheProof "thmSND" ctxtPair Base.thmSND

thmPAIR :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR = cacheProof "thmPAIR" ctxtPair Base.thmPAIR

recursionPAIR :: PairCtxt thry => HOL cls thry HOLThm
recursionPAIR = cacheProof "recursionPAIR" ctxtPair Base.recursionPAIR

inductPAIR :: PairCtxt thry => HOL cls thry HOLThm
inductPAIR = cacheProof "inductPAIR" ctxtPair Base.inductPAIR

-- conversions and derived rules
convGEQ :: PairCtxt thry => Conversion cls thry
convGEQ = convREWR (ruleGSYM defGEQ)

ruleDEGEQ :: PairCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleDEGEQ = ruleCONV (convREWR defGEQ)

ruleGABS :: PairCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleGABS = liftM1 ruleMATCH_MP ruleGABS_pth
  where ruleGABS_pth :: PairCtxt thry => HOL cls thry HOLThm
        ruleGABS_pth = cacheProof "ruleGABS_pth" ctxtPair $
            prove "(?) P ==> P (GABS P)" $
              tacSIMP [defGABS, axSELECT, axETA]

convGEN_BETA :: PairCtxt thry => Conversion cls thry
convGEN_BETA = Conv $ \ tm ->
    runConv convBETA tm
    <|> noteHOL "convGEN_BETA"
          (do (l, r) <- liftMaybe "not a combination." $ destComb tm
              (vstr, bod) <- liftMaybe "rator not an abstraction." $ destGAbs l
              instn <- liftO $ termMatch [] vstr r
              ref <- newHOLRef $ ProjectionCache mapEmpty
              prjs <- createIteratedProjections ref vstr
              bth <- runConv (convSUBS prjs) bod
              gv <- genVar $ typeOf vstr
              bod' <- liftO $ subst [(vstr, gv)] =<< rand (concl bth)
              let pat = fromRight $ mkAbs gv bod'
              th1 <- runConv convBETA #<< mkComb pat vstr
              let th2 = fromRight $ primTRANS th1 =<< ruleSYM bth
                  avs = fst . stripForall . fromJust $ body =<< rand l
              th3 <- ruleGENL avs th2
              efn <- genVar $ typeOf pat
              efn' <- mkExists efn #<< subst [(pat, efn)] (concl th3)
              th4 <- ruleEXISTS efn' pat th3
              th5 <- ruleCONV (funpow (length avs + 1) convBINDER convGEQ) th4
              th6 <- ruleCONV convBETA =<< ruleGABS th5
              ruleINSTANTIATE instn =<< ruleDEGEQ =<< ruleSPEC_ALL th6) 

-- projections
type ProjectionState = HOLRef ProjectionCache
data ProjectionCache = ProjectionCache !(Map Text [HOLThm]) deriving Typeable

createProjections :: ClassicCtxt thry => ProjectionState 
                  -> Text -> HOL cls thry [HOLThm]
createProjections ref conname =
    do (ProjectionCache projs) <- readHOLRef ref
       case mapLookup conname projs of
         Just ths -> return ths
         _ ->
              do genty <- getConstType conname
                 let conty = fromJust . liftM (fst . destTypeOp) $
                               (liftM fst . destType) =<< 
                                 repeatM (liftM snd . destFunTy) genty
                 itys <- getIndDefs
                 (_, _, rth) <- liftMaybe ("createProjections: not in " ++ 
                                           "inductive type store") $ 
                                  mapLookup conty itys
                 sth <- ruleSPEC_ALL rth
                 let (evs, bod) = stripExists $ concl sth
                     cjs = conjuncts bod
                     (ourcj, n) = fromJust . findM (\ (x, _) -> 
                          do x' <- rand =<< (lHand . snd $ stripForall x)
                             (x'', _) <- destConst . fst $ stripComb x'
                             return $ x'' == conname) $ zip cjs [0..]
                     (avs, eqn) = stripForall ourcj
                     (con', args) = stripComb . fromJust $ rand eqn
                     (aargs, zargs) = fromJust $ chopList (length avs) args
                 gargs <- mapM (genVar . typeOf) zargs
                 gcon <- genVar =<< foldrM (mkFunTy . typeOf) 
                            (typeOf . fromJust $ rand eqn) avs
                 let btm = fromRight $ listMkAbs (aargs++gargs) =<< listMkComb gcon avs
                     bth = fromJust $ primINST [(con', btm)] sth
                 cths <- ruleCONJUNCTS #<< 
                           primASSUME (snd . stripExists $ concl bth)
                 let cth = cths !! n
                 dth <- ruleCONV (funpow (length avs) convBINDER 
                          (convRAND convBETAS)) cth
                 let etm = fromJust $ rator =<< 
                             lHand (snd . stripForall $ concl dth)
                 eth <- ruleSIMPLE_EXISTS etm dth
                 fth <- liftM (rulePROVE_HYP bth) $ 
                          foldrM ruleSIMPLE_CHOOSE eth evs
                 let zty = typeOf . fromJust . rand . snd . stripForall $ 
                             concl dth
                     mkProjector a = 
                         let ity = typeOf a
                             atm = fromRight $ listMkAbs avs a
                             th1 = fromJust $
                                     rulePINST [(zty, ity)] [(gcon, atm)] fth in
                           do th2 <- ruleSPEC_ALL =<< ruleSELECT =<< 
                                       ruleBETA th1
                              liftO $ ruleSYM th2
                 ths <- mapM mkProjector avs
                 writeHOLRef ref $ ProjectionCache (mapInsert conname ths projs)
                 return ths

createIteratedProjections :: ClassicCtxt thry
                          => ProjectionState -> HOLTerm 
                          -> HOL cls thry [HOLThm]
createIteratedProjections ref tm
    | null $ frees tm = return []
    | isVar tm = return [primREFL tm]
    | otherwise =
      let (con, _) = stripComb tm in
        do prjths <- createProjections ref . fst . fromJust $ destConst con
           let atm = fromJust $ rand =<< rand (concl $ head prjths)
           instn <- liftO $ termMatch [] atm tm
           arths <- mapM (ruleINSTANTIATE instn) prjths
           ths <- mapM (\ arth -> 
                    do sths <- createIteratedProjections ref #<< 
                                 lHand (concl arth)
                       mapM (ruleCONV (convRAND $ convSUBS [arth])) sths) arths
           return $! unions ths
