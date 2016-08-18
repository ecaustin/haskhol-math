module HaskHOL.Lib.Lists.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Lists.Context

-- Lift Parse Context and define quasi-quoter
pcLists :: ParseContext
pcLists = $(liftParseContext ctxtLists)

lists :: QuasiQuoter
lists = baseQuoter ctxtLists pcLists
