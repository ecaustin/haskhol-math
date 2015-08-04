{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Pair.Context
    ( PairType
    , PairThry
    , PairCtxt
    , ctxtPair
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.Base

data PairThry
type instance PairThry == PairThry = 'True

instance CtxtName PairThry where
    ctxtName _ = "PairCtxt"

type instance PolyTheory PairType b = PairCtxt b

type family PairCtxt a :: Constraint where
    PairCtxt a = (Typeable a, DeductiveCtxt a, PairContext ~ 'True)

type PairType = ExtThry PairThry DeductiveType

type family PairContext a :: Bool where
    PairContext BaseThry = 'False
    PairContext (ExtThry a b) = PairContext b || (a == PairThry)

ctxtPair :: TheoryPath PairType
ctxtPair = extendTheory ctxtDeductive $(thisModule') $
-- stage1
    do sequence_ [ defLET'
                 , defLET_END'
                 , defGABS'
                 , defGEQ'
                 , def_SEQPATTERN'
                 , def_UNGUARDED_PATTERN'
                 , def_GUARDED_PATTERN'
                 , def_MATCH'
                 , def_FUNCTION'
                 , defMK_PAIR'
                 ]
-- stage2
       void tyDefProd'
       parseAsInfix (",", (14, "right"))
       sequence_ [ defCOMMA'
                 , defFST'
                 , defSND'
                 ]
-- stage3
       extendBasicRewrites =<< sequence [thmFST, thmSND, thmPAIR]
       ths <- sequence [ defSND, defFST, defCOMMA, defMK_PAIR
                       , defGEQ, defGABS, defLET_END, defLET
                       , def_one, defI, defO, defCOND, def_FALSITY_
                       , defTY_EXISTS, defTY_FORALL
                       , defEXISTS_UNIQUE, defNOT, defFALSE, defOR
                       , defEXISTS, defFORALL, defIMP, defAND
                       , defT
                       ]
       let ths' = zip [ "SND", "FST", ",", "mk_pair", "GEQ"
                       , "GABS", "LET_END", "LET", "one", "I"
                       , "o", "COND", "_FALSITY_", "??", "!!"
                       , "?!", "~", "F", "\\/", "?", "!"
                       , "==>", "/\\", "T"
                       ] ths
       acid <- openLocalStateHOL (Definitions mapEmpty)
       updateHOL acid (AddDefinitions ths')
       closeAcidStateHOL acid
       sequence_ [ defCURRY'
                 , defUNCURRY'
                 , defPASSOC'
                 ]
-- stage4
       indth <- inductPAIR
       recth <- recursionPAIR
       addIndDefs [("prod", (1, indth, recth))]
       extendBasicConvs  ("convGEN_BETA", ([str| GABS (\ a. b) c |]
                         , ("convGEN_BETA", "HaskHOL.Lib.Pair")))
