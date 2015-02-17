{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.B.Context
    ( IndTypesBType
    , IndTypesBCtxt
    , ctxtIndTypesB
    , indTypesB
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypes.A.Context
import HaskHOL.Lib.IndTypes.B.Base

-- generate template types
extendTheory ctxtIndTypesA "IndTypesB" $
    do (indth, recth) <- indDefSum'
       sequence_ [ defOUTL' recth
                 , defOUTR' recth
                 ]
       addIndDefs [("sum", (2, indth, recth))]

templateProvers 'ctxtIndTypesB

-- have to manually write this, for now
type family IndTypesBCtxt a where
    IndTypesBCtxt a = (IndTypesACtxt a, IndTypesBContext a ~ True)

type instance PolyTheory IndTypesBType b = IndTypesBCtxt b

instance BasicConvs IndTypesBType where
    basicConvs _ = basicConvs (undefined :: PairType)
