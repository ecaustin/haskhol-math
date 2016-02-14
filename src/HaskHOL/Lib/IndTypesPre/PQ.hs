module HaskHOL.Lib.IndTypesPre.PQ where

import HaskHOL.Core
import HaskHOL.Lib.IndTypesPre.Context

-- Lift Parse Context and define quasi-quoter
pcIndTypesPre :: ParseContext
pcIndTypesPre = $(liftParseContext ctxtIndTypesPre)

indTypesPre :: QuasiQuoter
indTypesPre = baseQuoter ctxtIndTypesPre pcIndTypesPre
