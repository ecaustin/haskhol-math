{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Lists.A.Context
    ( ListsAType
    , ListsAThry
    , ListsACtxt
    , ctxtListsA
    , listsA
    ) where

import HaskHOL.Core

import HaskHOL.Lib.IndTypes.Context

import HaskHOL.Lib.Lists.A.Base

templateTypes ctxtIndTypes "ListsA"

ctxtListsA :: TheoryPath ListsAType
ctxtListsA = extendTheory ctxtIndTypes $
    do sequence_ [ defHD'
                 , defTL'
                 , defAPPEND'
                 , defREVERSE'
                 , defLENGTH'
                 , defMAP'
                 , defLAST'
                 , defBUTLAST'
                 , defREPLICATE'
                 , defNULL'
                 , defALL'
                 , defEX'
                 , defITLIST'
                 , defMEM'
                 , defALL2'
                 , defMAP2'
                 , defEL'
                 , defFILTER'
                 , defASSOC'
                 , defITLIST2'
                 , defZIP'
                 ]
       void tyDefCHAR'
       newTypeAbbrev "string" "char list"

templateProvers 'ctxtListsA

-- have to manually write this, for now
type family ListsACtxt a where
    ListsACtxt a = (IndTypesCtxt a, ListsAContext a ~ True)

type instance PolyTheory ListsAType b = ListsACtxt b
