{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Lists.Context
    ( ListsType
    , ListsCtxt
    , ctxtLists
    , lists
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.IndTypes

import HaskHOL.Lib.Lists.A.Context
import HaskHOL.Lib.Lists.Base

-- generate template types
extendTheory ctxtListsA "Lists" $
    mapM_ addMonoThm [thmMONO_ALL, thmMONO_ALL2]

templateProvers 'ctxtLists

-- have to manually write this, for now
type family ListsCtxt a where
    ListsCtxt a = (ListsACtxt a, ListsContext a ~ True)

type instance PolyTheory ListsType b = ListsCtxt b

instance BasicConvs ListsType where
    basicConvs _ = basicConvs (undefined :: IndTypesType)
