{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.WF.Context
    ( WFType
    , WFCtxt
    , ctxtWF
    , wF
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Pair

import HaskHOL.Lib.Arith.Context
import HaskHOL.Lib.WF.Base

-- generate template types
extendTheory ctxtArith "WF" $
    do parseAsInfix ("<<", (12, "right"))
       parseAsInfix ("<<<", (12, "right"))
       sequence_ [ defWF'
                 , defMEASURE'
                 , defNUMPAIR'
                 , defNUMSUM'
                 ]

templateProvers 'ctxtWF

-- have to manually write this, for now
type family WFCtxt a where
    WFCtxt a = (ArithCtxt a, WFContext a ~ True)

type instance PolyTheory WFType b = WFCtxt b

instance BasicConvs WFType where
    basicConvs _ = basicConvs (undefined :: PairType)
