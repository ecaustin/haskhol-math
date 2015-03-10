{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Nums.Context
    ( NumsType
    , NumsThry
    , NumsCtxt
    , ctxtNums
    , nums
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Nums.B.Context
import HaskHOL.Lib.Nums.Base

templateTypes ctxtNumsB "Nums"

ctxtNums :: TheoryPath NumsType
ctxtNums = extendTheory ctxtNumsB $
    do indth <- inductionNUM
       recth <- recursionStdNUM
       addIndDefs [("num", (2, indth, recth))]
       sequence_ [defBIT0'', defBIT1']

templateProvers 'ctxtNums

-- have to manually write this, for now
type family NumsCtxt a where
    NumsCtxt a = (NumsBCtxt a, NumsContext a ~ True)

type instance PolyTheory NumsType b = NumsCtxt b
