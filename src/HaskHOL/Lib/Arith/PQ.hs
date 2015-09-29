module HaskHOL.Lib.Arith.PQ where

import HaskHOL.Core
import HaskHOL.Lib.Arith.Context

-- Lift Parse Context and define quasi-quoter
pcArith :: ParseContext
pcArith = $(liftParseContext ctxtArith)

arith :: QuasiQuoter
arith = baseQuoter ctxtArith pcArith
