{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Pair.B.Context
    ( PairBType
    , PairBCtxt
    , ctxtPairB
    , pairB
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.A
import HaskHOL.Lib.Pair.B.Base

-- generate template types
extendTheory ctxtPairA "PairB" $
    do void tyDefProd'
       parseAsInfix (",", (14, "right"))
       sequence_ [ defCOMMA'
                 , defFST'
                 , defSND'
                 ]

templateProvers 'ctxtPairB

-- have to manually write this, for now
type family PairBCtxt a where
    PairBCtxt a = (PairACtxt a, PairBContext a ~ True)

type instance PolyTheory PairBType b = PairBCtxt b

instance BasicConvs PairBType where
    basicConvs _ = basicConvs (undefined :: DeductiveType)
