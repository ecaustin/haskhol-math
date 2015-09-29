module HaskHOL.Lib.WF.PQ where

import HaskHOL.Core
import HaskHOL.Lib.WF.Context

-- Lift Parse Context and define quasi-quoter
pcWF :: ParseContext
pcWF = $(liftParseContext ctxtWF)

wf :: QuasiQuoter
wf = baseQuoter ctxtWF pcWF
