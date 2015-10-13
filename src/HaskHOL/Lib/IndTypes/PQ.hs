module HaskHOL.Lib.IndTypes.PQ where

import HaskHOL.Core
import HaskHOL.Lib.IndTypes.Context

-- Lift Parse Context and define quasi-quoter
pcIndTypes :: ParseContext
pcIndTypes = $(liftParseContext ctxtIndTypes)

indTypes :: QuasiQuoter
indTypes = baseQuoter ctxtIndTypes pcIndTypes
