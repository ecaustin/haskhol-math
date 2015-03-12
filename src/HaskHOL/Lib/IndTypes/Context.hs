{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, QuasiQuotes, 
             TemplateHaskell, TypeFamilies, TypeSynonymInstances, 
             UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.Context
    ( IndTypesType
    , IndTypesThry
    , IndTypesCtxt
    , ctxtIndTypes
    , indTypes
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.IndTypes.Pre
import HaskHOL.Lib.IndTypes.B.Context
import HaskHOL.Lib.IndTypes.Base


templateTypes ctxtIndTypesB "IndTypes"

ctxtIndTypes :: TheoryPath IndTypesType
ctxtIndTypes = extendTheory ctxtIndTypesB $(thisModule') $
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
       mapM_ extendBasicConvs 
                [ ("convMATCH_SEQPATTERN", ("_MATCH x (_SEQPATTERN r s)", 
                   ("return convMATCH_SEQPATTERN_TRIV"
                   , ["HaskHOL.Lib.IndTypes"])))
                , ("convFUN_SEQPATTERN", ("_FUNCTION (_SEQPATTERN r s) x", 
                   ("return convMATCH_SEQPATTERN_TRIV"
                   , ["HaskHOL.Lib.IndTypes"])))
                , ("convMATCH_ONEPATTERN", ([str| _MATCH x (\y z. P y z) |], 
                   ("return convMATCH_ONEPATTERN_TRIV"
                   , ["HaskHOL.Lib.IndTypes"])))
                , ("convFUN_ONEPATTERN", ([str|_FUNCTION (\y z. P y z) x|], 
                   ("return convMATCH_ONEPATTERN_TRIV"
                   , ["HaskHOL.Lib.IndTypes"])))
                ]

templateProvers 'ctxtIndTypes

-- have to manually write this, for now
type family IndTypesCtxt a where
    IndTypesCtxt a = (IndTypesBCtxt a, IndTypesContext a ~ True)

type instance PolyTheory IndTypesType b = IndTypesCtxt b
