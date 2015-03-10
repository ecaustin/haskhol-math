{-|
  Module:    HaskHOL.Math
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown

  This module is the one to import for users looking to include the basic
  mathematical theories of the HaskHOL proof system, ranging from pairs to
  semirings.  It re-exports all of the math sub-modules; additionally, it 
  exports aliases to a theory context, quasi-quoter, and compile-time proof 
  methods for users who are working only with these libraries.
-}
module HaskHOL.Math
    ( -- * Theory Context
       -- $ThryCtxt
      MathType
    , MathCtxt
    , ctxtMath
    , math
    , module HaskHOL.Lib.Pair
    , module HaskHOL.Lib.Nums
    , module HaskHOL.Lib.Recursion
    , module HaskHOL.Lib.Arith
    , module HaskHOL.Lib.WF
    , module HaskHOL.Lib.CalcNum
    , module HaskHOL.Lib.Normalizer
    --, module HaskHOL.Lib.Grobner
    , module HaskHOL.Lib.IndTypes
    , module HaskHOL.Lib.Lists
    , module HaskHOL.Lib.Lists.Context
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.Normalizer
--import HaskHOL.Lib.Grobner
import HaskHOL.Lib.IndTypes
import HaskHOL.Lib.Lists

import HaskHOL.Lib.Lists.Context

{- $ThryCtxt
  See 'extendCtxt' in the "HaskHOL.Core.Ext" module for more information.
-}

{-| 
  The theory context type for the math libraries.  
  An alias to 'ListsType'.
-}
type MathType = ListsType
type MathCtxt a = ListsCtxt a

{-| 
  The theory context for the math libraries.  
  An alias to 'ctxtLists'.
-}
ctxtMath :: TheoryPath MathType
ctxtMath = ctxtLists

-- | The quasi-quoter for the math libraries.  An alias to 'wF'.
math :: QuasiQuoter
math = lists
