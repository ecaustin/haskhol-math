{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Arith.Context
    ( ArithType
    , ArithThry
    , ArithCtxt
    , ctxtArith
    , arith
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Arith.A.Context
import HaskHOL.Lib.Arith.Base

templateTypes ctxtArithA "Arith"

ctxtArith :: TheoryPath ArithType
ctxtArith = extendTheory ctxtArithA $(thisModule') $
    do parseAsBinder "minimal"
       void specDIVISION_0'
       void defMinimal'

templateProvers 'ctxtArith

-- have to manually write this, for now
type family ArithCtxt a where
    ArithCtxt a = (ArithACtxt a, ArithContext a ~ True)

type instance PolyTheory ArithType b = ArithCtxt b