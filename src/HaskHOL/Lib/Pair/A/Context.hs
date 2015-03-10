{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Pair.A.Context
    ( PairAType
    , PairAThry
    , PairACtxt
    , ctxtPairA
    , pairA
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.A.Base

templateTypes ctxtDeductive "PairA"

ctxtPairA :: TheoryPath PairAType
ctxtPairA = extendTheory ctxtDeductive $
    sequence_ [ defLET'
              , defLET_END'
              , defGABS'
              , defGEQ'
              , def_SEQPATTERN'
              , def_UNGUARDED_PATTERN'
              , def_GUARDED_PATTERN'
              , def_MATCH'
              , def_FUNCTION'
              , defMK_PAIR'
              ]

templateProvers 'ctxtPairA

-- have to manually write this, for now
type family PairACtxt a where
    PairACtxt a = (DeductiveCtxt a, PairAContext a ~ True)

type instance PolyTheory PairAType b = PairACtxt b
