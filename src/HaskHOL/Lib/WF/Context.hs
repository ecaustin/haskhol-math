{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.WF.Context
    ( WFType
    , WFThry
    , WFCtxt
    , ctxtWF
    , wF
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Arith.Context
import HaskHOL.Lib.WF.Base

templateTypes ctxtArith "WF"

ctxtWF :: TheoryPath WFType
ctxtWF = extendTheory ctxtArith $
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
