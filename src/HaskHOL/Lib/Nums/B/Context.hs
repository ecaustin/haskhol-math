{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Nums.B.Context
    ( NumsBType
    , NumsBCtxt
    , ctxtNumsB
    , numsB
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Pair

import HaskHOL.Lib.Nums.A.Context
import HaskHOL.Lib.Nums.B.Base

-- generate template types
extendTheory ctxtNumsA "NumsB" $
    do sequence_ [defIND_SUC', defIND_0']
       (rep, _, _) <- indDefNUM_REP''
       void $ tyDefNum'' rep
       sequence_ [defZERO', defSUC', defNUMERAL']

templateProvers 'ctxtNumsB

-- have to manually write this, for now
type family NumsBCtxt a where
    NumsBCtxt a = (NumsACtxt a, NumsBContext a ~ True)

type instance PolyTheory NumsBType b = NumsBCtxt b

instance BasicConvs NumsBType where
    basicConvs _ = basicConvs (undefined :: PairType)

