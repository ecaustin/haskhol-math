{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, QuasiQuotes, 
             TemplateHaskell, TypeFamilies, TypeSynonymInstances, 
             UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.Context
    ( IndTypesType
    , IndTypesCtxt
    , ctxtIndTypes
    , indTypes
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypes.Pre
import HaskHOL.Lib.IndTypes.B.Context
import HaskHOL.Lib.IndTypes.Base

import Unsafe.Coerce (unsafeCoerce)

templateTypes ctxtIndTypesB "IndTypes"

ctxtIndTypes :: TheoryPath IndTypesType
ctxtIndTypes = extendTheory ctxtIndTypesB $
    do (oindth, orecth) <- indDefOption'
       (lindth, lrecth) <- indDefList'
       addIndDefs [ ("option", (2, oindth, orecth))
                  , ("list", (2, lindth, lrecth))
                  ]
       void defISO'
       sindth <- inductSUM
       srecth <- recursionSUM
       acid1 <- openLocalStateHOL (InductiveTypes mapEmpty)
       updateHOL acid1 (PutInductiveTypes $ mapFromList
         [ ("list = NIL | CONS A list", (lindth, lrecth))
         , ("option = NONE | SOME A", (oindth, orecth))
         , ("sum = INL A | INR B", (sindth, srecth))
         ])
       createCheckpointAndCloseHOL acid1
       th <- ruleTAUT "(T <=> F) <=> F"
       acid2 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid2 (PutDistinctnessStore [("bool", th)])
       createCheckpointAndCloseHOL acid2
       mapM_ extendRectypeNet =<< liftM mapToAscList getIndDefs

templateProvers 'ctxtIndTypes

-- have to manually write this, for now
type family IndTypesCtxt a where
    IndTypesCtxt a = (IndTypesBCtxt a, IndTypesContext a ~ True)

type instance PolyTheory IndTypesType b = IndTypesCtxt b

instance BasicConvs IndTypesType where
    basicConvs _ = basicConvs (undefined :: PairType) ++
        [ ("convMATCH_SEQPATTERN",
           ("_MATCH x (_SEQPATTERN r s)", convMATCH_SEQPATTERN_TRIV'))
        , ("convFUN_SEQPATTERN",
           ("_FUNCTION (_SEQPATTERN r s) x", convMATCH_SEQPATTERN_TRIV'))
        , ("convMATCH_ONEPATTERN",
           ([str| _MATCH x (\y z. P y z) |], convMATCH_ONEPATTERN_TRIV'))
        , ("convFUN_ONEPATTERN",
           ([str| _FUNCTION (\y z. P y z) x |], convMATCH_ONEPATTERN_TRIV'))
        ]

convMATCH_SEQPATTERN_TRIV' :: Conversion cls thry
convMATCH_SEQPATTERN_TRIV' = 
    unsafeCoerce (convMATCH_SEQPATTERN_TRIV :: Conversion cls IndTypesBType)

convMATCH_ONEPATTERN_TRIV' :: Conversion cls thry
convMATCH_ONEPATTERN_TRIV' =
    unsafeCoerce (convMATCH_ONEPATTERN_TRIV :: Conversion cls IndTypesBType)
