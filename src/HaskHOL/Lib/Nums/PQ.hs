module HaskHOL.Lib.Nums.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Nums.Context

-- Lift Parse Context and define quasi-quoter
pcNums :: ParseContext
pcNums = $(liftParseContext ctxtNums)

nums :: QuasiQuoter
nums = baseQuoter ctxtNums pcNums
