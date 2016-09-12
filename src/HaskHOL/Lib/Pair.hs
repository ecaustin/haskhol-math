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
    , Base.newDefinition
    , getDefinition
    , Base.getDefinitions
    , Base.addDefinition
    , thmFORALL_PAIR
    , thmFORALL_UNCURRY
    , thmEXISTS_UNCURRY
    , createIteratedProjections
    , createProjections
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition, getDefinition)

import qualified HaskHOL.Lib.Pair.Base as Base
import HaskHOL.Lib.Pair.Context
import HaskHOL.Lib.Pair.PQ


-- Definition mechanics
getDefinition :: Text -> HOL cls thry HOLThm
getDefinition lbl =
    do defs <- Base.getDefinitions
       case mapAssoc lbl defs of
         Just res -> return res
         _ -> fail $ "getDefinition: definition for " ++ show lbl ++ 
                     " not found."


-- Definitions
tyDefProd :: PairCtxt thry => HOL cls thry HOLThm
tyDefProd = Base.tyDefProd

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
defMK_PAIR = Base.defMK_PAIR

defCOMMA :: PairCtxt thry => HOL cls thry HOLThm
defCOMMA = Base.defCOMMA

defFST :: PairCtxt thry => HOL cls thry HOLThm
defFST = Base.defFST

defSND :: PairCtxt thry => HOL cls thry HOLThm
defSND = Base.defSND

defCURRY :: PairCtxt thry => HOL cls thry HOLThm
defCURRY = cacheProof "defCURRY" ctxtPair $ getDefinition "CURRY"

defUNCURRY :: PairCtxt thry => HOL cls thry HOLThm
defUNCURRY = cacheProof "defUNCURRY" ctxtPair $ getDefinition "UNCURRY"

defPASSOC :: PairCtxt thry => HOL cls thry HOLThm
defPASSOC = cacheProof "defPASSOC" ctxtPair $ getDefinition "PASSOC"

-- syntax
mkPair :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkPair = mkBinary ","

destPair :: HOLTermRep tm cls thry => tm -> HOL cls thry (HOLTerm, HOLTerm)
destPair = destBinary ","

-- theorems
thmPAIR_EXISTS :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_EXISTS = Base.thmPAIR_EXISTS

thmFORALL_PAIR :: PairCtxt thry => HOL cls thry HOLThm
thmFORALL_PAIR = cacheProof "thmFORALL_PAIR" ctxtPair .
    prove [txt| !P. (!p. P p) <=> (!p1 p2. P(p1,p2)) |] $
      tacMESON [thmPAIR]

thmFORALL_UNCURRY :: PairCtxt thry => HOL cls thry HOLThm
thmFORALL_UNCURRY = cacheProof "thmFORALL_UNCURRY" ctxtPair .
    prove [txt| !P. (!f:A->B->C. P f) <=> (!f. P (\a b. f(a,b))) |] $
      tacGEN `_THEN` tacEQ `_THEN` tacSIMP ([] :: [HOLThm]) `_THEN` 
      tacDISCH `_THEN` tacX_GEN [txt| f:A->B->C |] `_THEN`
      _FIRST_ASSUM(tacMP . ruleSPEC [txt| \(a,b). (f:A->B->C) a b |]) `_THEN` 
      tacSIMP [axETA]

thmEXISTS_UNCURRY :: PairCtxt thry => HOL cls thry HOLThm
thmEXISTS_UNCURRY = cacheProof "thmEXISTS_UNCURRY" ctxtPair .
    prove [txt| !P. (?f:A->B->C. P f) <=> (?f. P (\a b. f(a,b))) |] $
      tacONCE_REWRITE [ruleMESON_NIL [txt| (?x. P x) <=> ~(!x. ~P x) |]] `_THEN`
      tacREWRITE [thmFORALL_UNCURRY]

thmREP_ABS_PAIR :: PairCtxt thry => HOL cls thry HOLThm
thmREP_ABS_PAIR = Base.thmREP_ABS_PAIR

thmPAIR_SURJECTIVE :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_SURJECTIVE = Base.thmPAIR_SURJECTIVE

thmPAIR_EQ :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_EQ = Base.thmPAIR_EQ

thmFST :: PairCtxt thry => HOL cls thry HOLThm
thmFST = Base.thmFST

thmSND :: PairCtxt thry => HOL cls thry HOLThm
thmSND = Base.thmSND

thmPAIR :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR = Base.thmPAIR

recursionPAIR :: PairCtxt thry => HOL cls thry HOLThm
recursionPAIR = Base.recursionPAIR

inductPAIR :: PairCtxt thry => HOL cls thry HOLThm
inductPAIR = Base.inductPAIR

-- conversions and derived rules
convGEQ :: PairCtxt thry => Conversion cls thry
convGEQ = convREWR (ruleGSYM defGEQ)

ruleDEGEQ :: (PairCtxt thry, HOLThmRep thm cls thry) 
          => thm -> HOL cls thry HOLThm
ruleDEGEQ = ruleCONV (convREWR defGEQ)

ruleGABS :: (PairCtxt thry, HOLThmRep thm cls thry) 
         => thm -> HOL cls thry HOLThm
ruleGABS = ruleMATCH_MP ruleGABS_pth
  where ruleGABS_pth :: PairCtxt thry => HOL cls thry HOLThm
        ruleGABS_pth = cacheProof "ruleGABS_pth" ctxtPair .
            prove [txt| (?) P ==> P (GABS P) |] $
              tacSIMP [defGABS, axSELECT, axETA]

convGEN_BETA :: PairCtxt thry => Conversion cls thry
convGEN_BETA = Conv $ \ tm ->
    runConv convBETA tm
    <|> note "convGEN_BETA"
          (do (l, r) <- destComb tm
              (vstr, bod) <- destGAbs l
              instn <- termMatch [] vstr r
              ref <- newHOLRef $ ProjectionCache mapEmpty
              prjs <- createIteratedProjections ref vstr
              bth <- runConv (convSUBS prjs) bod
              gv <- genVar $ typeOf vstr
              bod' <- subst [(vstr, gv)] =<< rand (concl bth)
              pat <- mkAbs gv bod'
              th1 <- runConv convBETA $ mkComb pat vstr
              th2 <- primTRANS th1 $ ruleSYM bth
              avs <- liftM (fst . stripForall) $ body =<< rand l
              th3 <- ruleGENL avs th2
              efn <- genVar $ typeOf pat
              efn' <- mkExists efn =<< subst [(pat, efn)] (concl th3)
              th4 <- ruleEXISTS efn' pat th3
              th5 <- ruleCONV (funpow (length avs + 1) convBINDER convGEQ) th4
              th6 <- ruleCONV convBETA $ ruleGABS th5
              ruleINSTANTIATE instn . ruleDEGEQ $ ruleSPEC_ALL th6) 

-- projections
type ProjectionState = HOLRef ProjectionCache
data ProjectionCache = ProjectionCache !(Map Text [HOLThm]) deriving Typeable

createProjections :: ClassicCtxt thry => ProjectionState 
                  -> Text -> HOL cls thry [HOLThm]
createProjections ref conname =
    do (ProjectionCache projs) <- readHOLRef ref
       case mapAssoc conname projs of
         Just ths -> return ths
         _ ->
              do genty <- getConstType conname
                 (conop, _) <- destType =<< 
                                 repeatM (liftM snd . destFunTy) genty
                 let (conty, _) = destTypeOp conop
                 itys <- getIndDefs
                 (_, _, rth) <- mapAssoc conty itys <?> 
                                  "createProjections: not in inductive store"
                 sth <- ruleSPEC_ALL rth
                 let (evs, bod) = stripExists $ concl sth
                     cjs = conjuncts bod
                 (ourcj, n) <- findM (\ (x, _) -> 
                                 do x' <- rand =<< (lHand . snd $ stripForall x)
                                    (x'', _) <- destConst . fst $ stripComb x'
                                    return $ x'' == conname) $ zip cjs [0..]
                 let (avs, eqn) = stripForall ourcj
                 (con', args) <- liftM stripComb $ rand eqn
                 (aargs, zargs) <- trySplitAt (length avs) args
                 gargs <- mapM (genVar . typeOf) zargs
                 eqty <- typeOf $ rand eqn
                 gcon <- genVar =<< foldrM (mkFunTy . typeOf) eqty avs
                 btm <- listMkAbs (aargs++gargs) =<< listMkComb gcon avs
                 bth <- primINST [(con', btm)] sth
                 cths <- ruleCONJUNCTS $ 
                           primASSUME (snd . stripExists $ concl bth)
                 let cth = cths !! n
                 dth <- ruleCONV (funpow (length avs) convBINDER 
                          (convRAND convBETAS)) cth
                 etm <- rator =<< lHand (snd . stripForall $ concl dth)
                 eth <- ruleSIMPLE_EXISTS etm dth
                 fth <- rulePROVE_HYP bth $ foldrM ruleSIMPLE_CHOOSE eth evs
                 zty <- liftM typeOf . rand . snd . stripForall $ concl dth
                 let mkProjector a = 
                         let ity = typeOf a in
                           do atm <- listMkAbs avs a
                              th1 <- rulePINST [(zty, ity)] [(gcon, atm)] fth
                              th2 <- ruleSPEC_ALL . ruleSELECT $ ruleBETA th1
                              ruleSYM th2
                 ths <- mapM mkProjector avs
                 writeHOLRef ref $ ProjectionCache (mapInsert conname ths projs)
                 return ths

createIteratedProjections :: ClassicCtxt thry
                          => ProjectionState -> HOLTerm 
                          -> HOL cls thry [HOLThm]
createIteratedProjections ref tm
    | null $ frees tm = return []
    | isVar tm = sequence [primREFL tm]
    | otherwise =
      let (con, _) = stripComb tm in
        do prjths <- createProjections ref =<< liftM fst (destConst con)
           atm <- rand =<< rand (concl $ head prjths)
           instn <- termMatch [] atm tm
           arths <- mapM (ruleINSTANTIATE instn) prjths
           ths <- mapM (\ arth -> 
                   do sths <- createIteratedProjections ref =<< 
                                lHand (concl arth)
                      mapM (ruleCONV (convRAND $ convSUBS [arth])) sths) arths
           return $! unions ths
