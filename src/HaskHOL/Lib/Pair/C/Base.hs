{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, 
             PatternSynonyms, QuasiQuotes, TemplateHaskell, TypeFamilies #-}
module HaskHOL.Lib.Pair.C.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, newDefinition)
import qualified HaskHOL.Deductive as D

import HaskHOL.Lib.Pair.B


