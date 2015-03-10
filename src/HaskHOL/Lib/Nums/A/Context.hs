{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Nums.A.Context
    ( NumsAType
    , NumsAThry
    , NumsACtxt
    , ctxtNumsA
    , numsA
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums.A.Base

templateTypes ctxtPair "NumsA"

ctxtNumsA :: TheoryPath NumsAType
ctxtNumsA = extendTheory ctxtPair $
    do newType "ind" 0
       sequence_ [defONE_ONE', defONTO']
       void axINFINITY'

templateProvers 'ctxtNumsA

-- have to manually write this, for now
type family NumsACtxt a where
    NumsACtxt a = (PairCtxt a, NumsAContext a ~ True)

type instance PolyTheory NumsAType b = NumsACtxt b
