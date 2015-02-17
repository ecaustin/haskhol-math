{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.A.Context
    ( IndTypesAType
    , IndTypesACtxt
    , ctxtIndTypesA
    , indTypesA
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Pair

import HaskHOL.Lib.WF.Context
import HaskHOL.Lib.IndTypes.A.Base

-- generate template types
extendTheory ctxtWF "IndTypesA" $
    do sequence_ [ specNUMPAIR_DEST'
                 , specNUMSUM_DEST'
                 , defINJN'
                 , defINJA'
                 , defINJF'
                 , defINJP'
                 , defZCONSTR'
                 , defZBOT'
                 ]
       (rep, _, _) <- indDefZRECSPACE'
       _ <- tyDefRecspace' rep
       sequence_ [ defBOTTOM'
                 , defCONSTR'
                 , defFCONS'
                 , defFNIL'
                 ]

templateProvers 'ctxtIndTypesA

-- have to manually write this, for now
type family IndTypesACtxt a where
    IndTypesACtxt a = (WFCtxt a, IndTypesAContext a ~ True)

type instance PolyTheory IndTypesAType b = IndTypesACtxt b

instance BasicConvs IndTypesAType where
    basicConvs _ = basicConvs (undefined :: PairType)
