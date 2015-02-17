{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, QuasiQuotes, 
             TemplateHaskell, TypeFamilies, TypeSynonymInstances, 
             UndecidableInstances #-}
module HaskHOL.Lib.Pair.Context
    ( PairType
    , PairCtxt
    , ctxtPair
    , pair
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.C
import HaskHOL.Lib.Pair.Base

import Unsafe.Coerce (unsafeCoerce)

-- generate template types
extendTheory ctxtPairC "Pair" $
    do indth <- inductPAIR
       recth <- recursionPAIR
       addIndDefs [("prod", (1, indth, recth))]

templateProvers 'ctxtPair

-- have to manually write this, for now
type family PairCtxt a where
    PairCtxt a = (PairCCtxt a, PairContext a ~ True)

type instance PolyTheory PairType b = PairCtxt b

instance BasicConvs PairType where
    basicConvs _ = basicConvs (undefined :: DeductiveType) ++ 
        [("convGEN_BETA", ([str| GABS (\ a. b) c |], convGEN_BETA'))]


convGEN_BETA' :: Conversion cls thry
convGEN_BETA' = unsafeCoerce (convGEN_BETA :: Conversion cls PairCType)
