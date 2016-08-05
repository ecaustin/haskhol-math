{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.WF.Context
    ( WFType
    , WFThry
    , WFCtxt
    , ctxtWF
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Pair

import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.Arith.Context

data WFThry
type instance WFThry == WFThry = 'True

instance CtxtName WFThry where
    ctxtName _ = "WFCtxt"

type instance PolyTheory WFType b = WFCtxt b

type family WFCtxt a :: Constraint where
    WFCtxt a = (Typeable a, ArithCtxt a, WFContext a ~ 'True)

type WFType = ExtThry WFThry ArithType

type family WFContext a :: Bool where
    WFContext BaseThry = 'False
    WFContext (ExtThry a b) = WFContext b || (a == WFThry)

ctxtWF :: TheoryPath WFType
ctxtWF = extendTheory ctxtArith $(thisModule') $
    do parseAsInfix ("<<", (12, "right"))
       parseAsInfix ("<<<", (12, "right"))
       mapM_ newDefinition
         [ ("WF", [txt| WF(<<) <=> !P:A->bool. (?x. P(x)) ==> 
                                   (?x. P(x) /\ !y. y << x ==> ~P(y)) |])
         , ("MEASURE", [txt| MEASURE m = \x y. m(x) < m(y) |])
         , ("NUMPAIR", [txt| NUMPAIR x y = (2 EXP x) * (2 * y + 1) |])
         , ("NUMSUM", [txt| NUMSUM b x = if b then SUC(2 * x) else 2 * x |])
         ]
       -- Force evaluation of some theorems to save time in CalcNum compilation
       sequence_
         [ thmARITH_ADD, thmARITH_SUC, thmARITH_0, thmBITS_INJ
         , thmMULT_2, thmBIT0, thmBIT1, thmADD_CLAUSES, thmSUC_INJ
         , thmEQ_MULT_LCANCEL, thmARITH_EQ, thmLEFT_ADD_DISTRIB
         , thmMULT_ASSOC
         ]
       
