{-# LANGUAGE FlexibleContexts, PatternSynonyms #-}
module HaskHOL.Lib.Pair.B.Base where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.A

defLET :: PairACtxt thry => HOL cls thry HOLThm
defLET = cacheProof "defLET" ctxtPairA $ getDefinition "LET"

defLET_END :: PairACtxt thry => HOL cls thry HOLThm
defLET_END = cacheProof "defLET_END" ctxtPairA $ getDefinition "LET_END"

defGABS :: PairACtxt thry => HOL cls thry HOLThm
defGABS = cacheProof "defGABS" ctxtPairA $ getDefinition "GABS"

defGEQ :: PairACtxt thry => HOL cls thry HOLThm
defGEQ = cacheProof "defGEQ" ctxtPairA $ getDefinition "GEQ"

def_SEQPATTERN :: PairACtxt thry => HOL cls thry HOLThm
def_SEQPATTERN = cacheProof "def_SEQPATTERN" ctxtPairA $ 
    getDefinition "_SEQPATTERN"

def_UNGUARDED_PATTERN :: PairACtxt thry => HOL cls thry HOLThm
def_UNGUARDED_PATTERN = cacheProof "def_UNGUARDED_PATTERN" ctxtPairA $
    getDefinition "_UNGUARDED_PATTERN"

def_GUARDED_PATTERN :: PairACtxt thry => HOL cls thry HOLThm
def_GUARDED_PATTERN = cacheProof "def_GUARDED_PATTERN" ctxtPairA $ 
    getDefinition "_GUARDED_PATTERN"

def_MATCH :: PairACtxt thry => HOL cls thry HOLThm
def_MATCH = cacheProof "def_MATCH" ctxtPairA $ getDefinition "_MATCH"

def_FUNCTION :: PairACtxt thry => HOL cls thry HOLThm
def_FUNCTION = cacheProof "def_FUNCTION" ctxtPairA $ getDefinition "_FUNCTION"

defMK_PAIR :: PairACtxt thry => HOL cls thry HOLThm
defMK_PAIR = cacheProof "defMK_PAIR" ctxtPairA $ getDefinition "mk_pair"

thmPAIR_EXISTS :: (BasicConvs thry, PairACtxt thry) => HOL cls thry HOLThm
thmPAIR_EXISTS = cacheProof "thmPAIR_EXISTS" ctxtPairA $
    prove "? x. ? (a:A) (b:B). x = mk_pair a b" tacMESON_NIL

tyDefProd' :: (BasicConvs thry, PairACtxt thry) => HOL Theory thry HOLThm
tyDefProd' = newTypeDefinition "prod" "ABS_prod" "REP_prod" thmPAIR_EXISTS

defCOMMA' :: BoolCtxt thry => HOL Theory thry HOLThm
defCOMMA' = newDefinition ","
    [str| ((x:A), (y:B)) = ABS_prod(mk_pair x y) |]

defFST' :: BoolCtxt thry => HOL Theory thry HOLThm
defFST' = newDefinition "FST"
    [str| FST (p:A#B) = @ x. ? y. p = (x, y) |]

defSND' :: BoolCtxt thry => HOL Theory thry HOLThm
defSND' = newDefinition "SND"
    [str| SND (p:A#B) = @ y. ? x. p = (x, y) |]
