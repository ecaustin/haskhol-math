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

import HaskHOL.Lib.Pair.Base
import HaskHOL.Lib.Pair.Context
import HaskHOL.Lib.Pair.PQ

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

thmPAIR_EXISTS :: PairCtxt thry => HOL cls thry HOLThm
thmPAIR_EXISTS = cacheProof "thmPAIR_EXISTS" ctxtPair thmPAIR_EXISTS'

tyDefProd :: PairBCtxt thry => HOL cls thry HOLThm
tyDefProd = cacheProof "tyDefProd" ctxtPairB $ getTypeDefinition "prod"

defCOMMA :: PairBCtxt thry => HOL cls thry HOLThm
defCOMMA = cacheProof "defCOMMA" ctxtPairB $ D.getDefinition ","

defFST :: PairBCtxt thry => HOL cls thry HOLThm
defFST = cacheProof "defFST" ctxtPairB $ D.getDefinition "FST"

defSND :: PairBCtxt thry => HOL cls thry HOLThm
defSND = cacheProof "defSND" ctxtPairB $ D.getDefinition "SND"

defCURRY :: PairCtxt thry => HOL cls thry HOLThm
defCURRY = cacheProof "defCURRY" ctxtPair $ getDefinition "CURRY"

defUNCURRY :: PairCtxt thry => HOL cls thry HOLThm
defUNCURRY = cacheProof "defUNCURRY" ctxtPair $ getDefinition "UNCURRY"

defPASSOC :: PairCtxt thry => HOL cls thry HOLThm
defPASSOC = cacheProof "defPASSOC" ctxtPair $ getDefinition "PASSOC"

ruleGABS :: PairCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleGABS = ruleGABS' ruleGABS_pth
  where ruleGABS_pth :: PairCtxt thry => HOL cls thry HOLThm
        ruleGABS_pth = cacheProof "ruleGABS_pth" ruleGABS_pth'

convGEQ :: PairCtxt thry => Conversion cls thry
convGEQ = convGEQ' convGEQ_pth
  where convGEQ_pth :: PairCtxt thry => HOL cls thry HOLThm
        convGEQ_pth = cacheProof "convGEQ_pth" convGEQ_pth'

ruleDEGEQ :: PairCtxt thry => HOLThm -> HOL cls thry HOLThm
ruleDEGEQ = ruleCONV rule_DEGEQ_pth
  where ruleDEGEQ_pth :: PairCtxt thry => HOL cls thry HOLThm
        ruleDEGEQ_pth = cacheProof "ruleDEGEQ_pth" ruleDEGEQ_pth'


mkPair :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkPair = mkBinary ","

destPair :: HOLTerm -> Maybe (HOLTerm, HOLTerm)
destPair = destBinary ","

thmFORALL_PAIR :: PairCtxt thry => HOL cls thry HOLThm
thmFORALL_PAIR = cacheProof "thmFORALL_PAIR" ctxtPair $
    prove "!P. (!p. P p) <=> (!p1 p2. P(p1,p2))" $
      tacMESON [thmPAIR]
