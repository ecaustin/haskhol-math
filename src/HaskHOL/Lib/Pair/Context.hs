{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, QuasiQuotes, 
             TemplateHaskell, TypeFamilies, TypeSynonymInstances, 
             UndecidableInstances #-}
module HaskHOL.Lib.Pair.Context
    ( PairType
    , PairThry
    , PairCtxt
    , ctxtPair
    , pair
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.C

templateTypes ctxtPairC "Pair"

ctxtPair :: TheoryPath PairType
ctxtPair = extendTheory ctxtPairC $
    do indth <- inductPAIR
       recth <- recursionPAIR
       addIndDefs [("prod", (1, indth, recth))]
       extendBasicConvs  ("convGEN_BETA", ([str| GABS (\ a. b) c |]
                         , ("convGEN_BETA", ["HaskHOL.Lib.Pair"])))

templateProvers 'ctxtPair

-- have to manually write this, for now
type family PairCtxt a where
    PairCtxt a = (PairCCtxt a, PairContext a ~ True)

type instance PolyTheory PairType b = PairCtxt b
