{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.Nums.B.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition, getDefinition)
import HaskHOL.Lib.Pair

import HaskHOL.Lib.Nums.A

defONE_ONE :: NumsACtxt thry => HOL cls thry HOLThm
defONE_ONE = cacheProof "defONE_ONE" ctxtNumsA $ getDefinition "ONE_ONE"

defONTO :: NumsACtxt thry => HOL cls thry HOLThm
defONTO = cacheProof "defONTO" ctxtNumsA $ getDefinition "ONTO"

axINFINITY :: NumsACtxt thry => HOL cls thry HOLThm
axINFINITY = cacheProof "axINFINITY" ctxtNumsA $ getAxiom "axINFINITY"

defIND_SUC' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defIND_SUC' = newDefinition "IND_SUC"
    [str| IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\
                                     (!x. ~(f x = z)) |]

defIND_0' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defIND_0' = newDefinition "IND_0"
    [str| IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                          (!x. ~(IND_SUC x = z)) |]


indDefNUM_REP'' :: (BasicConvs thry, IndDefsCtxt thry) 
                => HOL Theory thry (HOLThm, HOLThm, HOLThm)
indDefNUM_REP'' = newInductiveDefinition "NUM_REP"
    [str| NUM_REP IND_0 /\ (!i. NUM_REP i ==> NUM_REP (IND_SUC i)) |]


tyDefNum'' :: IndDefsCtxt thry => HOLThm -> HOL Theory thry (HOLThm, HOLThm)
tyDefNum'' rep = 
    newBasicTypeDefinition "num" "mk_num" "dest_num" =<< 
      ruleCONJUNCT1 rep

defZERO' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defZERO' = newDefinition "_0"
    [str| _0 = mk_num IND_0 |]


defSUC' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defSUC' = newDefinition "SUC"
    [str| SUC n = mk_num (IND_SUC (dest_num n)) |]

defNUMERAL' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defNUMERAL' = newDefinition "NUMERAL"
    [str| NUMERAL (n:num) = n |]
