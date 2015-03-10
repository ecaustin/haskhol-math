{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.Nums.A.Base where

import HaskHOL.Core

import HaskHOL.Lib.Pair


defONE_ONE' :: PairCtxt thry => HOL Theory thry HOLThm
defONE_ONE' = newDefinition "ONE_ONE" $
    [str| ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2) |]

defONTO' :: PairCtxt thry => HOL Theory thry HOLThm
defONTO' = newDefinition "ONTO" $
    [str| ONTO(f:A->B) = !y. ?x. y = f x |]

axINFINITY' :: HOL Theory thry HOLThm
axINFINITY' = newAxiom "axINFINITY" [str| ?f:ind->ind. ONE_ONE f /\ ~(ONTO f) |]

