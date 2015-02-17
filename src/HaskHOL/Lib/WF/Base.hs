{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.WF.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)

import HaskHOL.Lib.Pair

defWF' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defWF' = newDefinition "WF"
    [str| WF(<<) <=> 
          !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\ !y. y << x ==> ~P(y)) |]
                 
defMEASURE' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defMEASURE' = newDefinition "MEASURE"
    [str| MEASURE m = \x y. m(x) < m(y) |]

defNUMPAIR' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defNUMPAIR' = newDefinition "NUMPAIR"
    [str| NUMPAIR x y = (2 EXP x) * (2 * y + 1) |]


defNUMSUM' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defNUMSUM' = newDefinition "NUMSUM"
    "NUMSUM b x = if b then SUC(2 * x) else 2 * x"
