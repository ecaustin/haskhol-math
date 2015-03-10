{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Pair.C.Context
    ( PairCType
    , PairCThry
    , PairCCtxt
    , ctxtPairC
    , pairC
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Pair.B
import HaskHOL.Lib.Pair.C.Base

templateTypes ctxtPairB "PairC"

ctxtPairC :: TheoryPath PairCType
ctxtPairC = extendTheory ctxtPairB $
    do extendBasicRewrites =<< sequence [thmFST, thmSND, thmPAIR]
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

templateProvers 'ctxtPairC

-- have to manually write this, for now
type family PairCCtxt a where
    PairCCtxt a = (PairBCtxt a, PairCContext a ~ True)

type instance PolyTheory PairCType b = PairCCtxt b

