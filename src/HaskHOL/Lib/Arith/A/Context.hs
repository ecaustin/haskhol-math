{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TemplateHaskell, 
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
module HaskHOL.Lib.Arith.A.Context
    ( ArithAType
    , ArithAThry
    , ArithACtxt
    , ctxtArithA
    , arithA
    ) where

import HaskHOL.Core

import HaskHOL.Lib.Nums.Context
import HaskHOL.Lib.Arith.A.Base

templateTypes ctxtNums "ArithA"

ctxtArithA :: TheoryPath ArithAType
ctxtArithA = extendTheory ctxtNums $(thisModule') $
    do mapM_ parseAsInfix [ ("<", (12, "right"))
                          , ("<=", (12, "right"))
                          , (">", (12, "right"))
                          , (">=",(12,"right"))
                          , ("+",(16, "right"))
                          , ("-", (18, "left"))
                          , ("*", (20,"right"))
                          , ("EXP", (24, "left"))
                          , ("DIV", (22, "left"))
                          , ("MOD", (22, "left"))
                          ]
       sequence_ [ defPRE'
                 , defADD'
                 , defMULT'
                 , defEXP'
                 , defLE'
                 , defLT'
                 , defGE'
                 , defGT'
                 , defMAX'
                 , defMIN'
                 , defEVEN'
                 , defODD'
                 , defSUB'
                 , defFACT'
                 ]

templateProvers 'ctxtArithA

-- have to manually write this, for now
type family ArithACtxt a where
    ArithACtxt a = (NumsCtxt a, ArithAContext a ~ True)

type instance PolyTheory ArithAType b = ArithACtxt b
