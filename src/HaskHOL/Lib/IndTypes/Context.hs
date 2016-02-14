{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.Context
    ( IndTypesType
    , IndTypesThry
    , IndTypesCtxt
    , ctxtIndTypes
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition)

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypesPre.Context

import HaskHOL.Lib.IndTypes.Pre
import HaskHOL.Lib.IndTypes.Base


data IndTypesThry
type instance IndTypesThry == IndTypesThry = 'True

instance CtxtName IndTypesThry where
    ctxtName _ = "IndTypesCtxt"

type instance PolyTheory IndTypesType b = IndTypesCtxt b

type family IndTypesCtxt a :: Constraint where
    IndTypesCtxt a = (Typeable a, IndTypesPreCtxt a, IndTypesContext a ~ 'True)

type IndTypesType = ExtThry IndTypesThry IndTypesPreType

type family IndTypesContext a :: Bool where
    IndTypesContext BaseThry = 'False
    IndTypesContext (ExtThry a b) = IndTypesContext b || (a == IndTypesThry)

ctxtIndTypes :: TheoryPath IndTypesType
ctxtIndTypes = extendTheory ctxtIndTypesPre $(thisModule') $
    do ctxt <- parseContext
       let indDefFun = defineTypeRaw <=< (parseInductiveTypeSpecification ctxt)
       (sindth, srecth) <- indDefFun [txt| sum = INL A | INR B |]
       mapM_ (newRecursiveDefinition srecth)
         [ ("OUTL", [txt| OUTL (INL x :A+B) = x |])
         , ("OUTR", [txt| OUTR (INR y :A+B) = y |])
         ]
       addIndDef ("sum", (2, sindth, srecth))
-- Stage3
       (oindth, orecth) <- indDefFun "option = NONE | SOME A"
       (lindth, lrecth) <- indDefFun "list = NIL | CONS A list"
       mapM_ addIndDef [ ("option", (2, oindth, orecth))
                       , ("list", (2, lindth, lrecth))
                       ]
       void $ newDefinition 
                ("ISO", [txt| ISO (f:A->B) (g:B->A) <=> 
                                (!x. f(g x) = x) /\ (!y. g(f y) = y) |])
       acid1 <- openLocalStateHOL (InductiveTypes mapEmpty)
       updateHOL acid1 (PutInductiveTypes $ mapFromList
         [ ("list = NIL | CONS A list", (lindth, lrecth))
         , ("option = NONE | SOME A", (oindth, orecth))
         , ("sum = INL A | INR B", (sindth, srecth))
         ])
       closeAcidStateHOL acid1
       boolth <- ruleTAUT [txt| (T <=> F) <=> F |]
       acid2 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid2 (PutDistinctnessStore [("bool", boolth)])
       closeAcidStateHOL acid2
       mapM_ extendRectypeNet =<< liftM mapToAscList getIndDefs
       extendBasicConvs 
                [ ("convMATCH_SEQPATTERN_TRIV", 
                   ("_MATCH x (_SEQPATTERN r s)", "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_SEQPATTERN_TRIV", 
                   ("_FUNCTION (_SEQPATTERN r s) x", "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_ONEPATTERN_TRIV", 
                   ([txt| _MATCH x (\y z. P y z) |], "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_ONEPATTERN_TRIV", 
                   ([txt|_FUNCTION (\y z. P y z) x|], "HaskHOL.Lib.IndTypes"))
                ]
