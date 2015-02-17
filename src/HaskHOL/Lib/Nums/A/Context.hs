{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Nums.A.Context
    ( NumsAType
    , NumsACtxt
    , ctxtNumsA
    , numsA
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Pair.Context
import HaskHOL.Lib.Nums.A.Base

-- generate template types
extendTheory ctxtPair "NumsA" $
    do newType "ind" 0
       sequence_ [defONE_ONE', defONTO']
       void axINFINITY'

templateProvers 'ctxtNumsA

-- have to manually write this, for now
type family NumsACtxt a where
    NumsACtxt a = (PairCtxt a, NumsAContext a ~ True)

type instance PolyTheory NumsAType b = NumsACtxt b

instance BasicConvs NumsAType where
    basicConvs _ = basicConvs (undefined :: PairType)
