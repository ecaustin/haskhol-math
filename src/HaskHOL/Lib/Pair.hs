
module HaskHOL.Lib.Pair
    ( PairType
    , PairCtxt
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

import HaskHOL.Lib.Pair.B
import HaskHOL.Lib.Pair.C
import HaskHOL.Lib.Pair.Base
import HaskHOL.Lib.Pair.Context


mkPair :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkPair = mkBinary ","

destPair :: HOLTerm -> Maybe (HOLTerm, HOLTerm)
destPair = destBinary ","

thmFORALL_PAIR :: (BasicConvs thry, PairCtxt thry) => HOL cls thry HOLThm
thmFORALL_PAIR = cacheProof "thmFORALL_PAIR" ctxtPair $
    prove "!P. (!p. P p) <=> (!p1 p2. P(p1,p2))" $
      tacMESON [thmPAIR]
