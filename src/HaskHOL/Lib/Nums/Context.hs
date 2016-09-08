{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Nums.Context
    ( NumsType
    , NumsThry
    , NumsCtxt
    , ctxtNums
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition)
import HaskHOL.Lib.Pair

import HaskHOL.Lib.Pair.Context
import HaskHOL.Lib.Nums.Base

data NumsThry
type instance NumsThry == NumsThry = 'True

instance CtxtName NumsThry where
    ctxtName _ = "NumsCtxt"

type instance PolyTheory NumsType b = NumsCtxt b

type family NumsCtxt a :: Constraint where
    NumsCtxt a = (Typeable a, PairCtxt a, NumsContext a ~ 'True)

type NumsType = ExtThry NumsThry PairType

type family NumsContext a :: Bool where
    NumsContext UnsafeThry = 'True
    NumsContext BaseThry = 'False
    NumsContext (ExtThry a b) = NumsContext b || (a == NumsThry)

ctxtNums :: TheoryPath NumsType
ctxtNums = extendTheory ctxtPair $(thisModule') $
-- Stage 1
    do newType "ind" 0
       mapM_ newDefinition
         [ ("ONE_ONE", [txt| ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> 
                                                       (x1 = x2) |])
         , ("ONTO", [txt| ONTO(f:A->B) = !y. ?x. y = f x |])
         ]
       void $ newAxiom 
         ("axINFINITY", [txt| ?f:ind->ind. ONE_ONE f /\ ~(ONTO f) |])
-- Stage 2
       mapM_ newDefinition
         [ ("IND_SUC", [txt| IND_SUC = @f:ind->ind. ?z. 
                                       (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ 
                                       (!x. ~(f x = z)) |])
         , ("IND_0", [txt| IND_0 = @z:ind. 
                                (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                                (!x. ~(IND_SUC x = z)) |]) 
         ]
       (rep, _, _) <- newInductiveDefinition "NUM_REP"
                        [txt| NUM_REP IND_0 /\ 
                              (!i. NUM_REP i ==> NUM_REP (IND_SUC i)) |]
       void $ newBasicTypeDefinition "num" "mk_num" "dest_num" =<< 
                ruleCONJUNCT1 rep
       mapM_ newDefinition
         [ ("_0", [txt| _0 = mk_num IND_0 |])
         , ("SUC", [txt| SUC n = mk_num (IND_SUC (dest_num n)) |])
         , ("NUMERAL", [txt| NUMERAL (n:num) = n |])
         ]
-- Stage 3
       addIndDef ("num", (2, inductionNUM, recursionStdNUM))
       mapM_ newDefinition
         [ ("BIT0", [txt| BIT0 = @fn. fn 0 = 0 /\ 
                                      (!n. fn (SUC n) = SUC (SUC(fn n))) |])
         , ("BIT1", [txt| BIT1 n = SUC (BIT0 n) |])
         ]
