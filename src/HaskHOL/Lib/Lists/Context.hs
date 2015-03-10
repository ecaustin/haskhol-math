{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Lists.Context
    ( ListsType
    , ListsThry
    , ListsCtxt
    , ctxtLists
    , lists
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Lists.A.Context
import HaskHOL.Lib.Lists.Base

templateTypes ctxtListsA "Lists"

ctxtLists :: TheoryPath ListsType
ctxtLists = extendTheory ctxtListsA $(thisModule') $
    mapM_ addMonoThm [thmMONO_ALL, thmMONO_ALL2]

templateProvers 'ctxtLists

-- have to manually write this, for now
type family ListsCtxt a where
    ListsCtxt a = (ListsACtxt a, ListsContext a ~ True)

type instance PolyTheory ListsType b = ListsCtxt b
