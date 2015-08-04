module HaskHOL.Lib.Pair.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Pair.Context

-- Lift Parse Context and define quasi-quoter
pcPair :: ParseContext
pcPair = $(liftParseContext ctxtPair)

pair :: QuasiQuoter
pair = baseQuoter ctxtPair pcPair
