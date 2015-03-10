{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Nums.B.Context
    ( NumsBType
    , NumsBThry
    , NumsBCtxt
    , ctxtNumsB
    , numsB
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Nums.A.Context
import HaskHOL.Lib.Nums.B.Base

templateTypes ctxtNumsA "NumsB"

ctxtNumsB :: TheoryPath NumsBType
ctxtNumsB = extendTheory ctxtNumsA $
    do sequence_ [defIND_SUC', defIND_0']
       (rep, _, _) <- indDefNUM_REP''
       void $ tyDefNum'' rep
       sequence_ [defZERO', defSUC', defNUMERAL']

templateProvers 'ctxtNumsB

-- have to manually write this, for now
type family NumsBCtxt a where
    NumsBCtxt a = (NumsACtxt a, NumsBContext a ~ True)

type instance PolyTheory NumsBType b = NumsBCtxt b
