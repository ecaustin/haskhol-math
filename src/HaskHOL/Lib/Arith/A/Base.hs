{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.Arith.A.Base where

import HaskHOL.Core

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion


defPRE' :: NumsCtxt thry => HOL Theory thry HOLThm
defPRE' = newRecursiveDefinition "PRE" recursionNUM
    [str| (PRE 0 = 0) /\ (!n. PRE (SUC n) = n) |]

defADD' :: NumsCtxt thry => HOL Theory thry HOLThm
defADD' = newRecursiveDefinition "+" recursionNUM
    [str| (!n. 0 + n = n) /\
          (!m n. (SUC m) + n = SUC(m + n)) |]

defMULT' :: NumsCtxt thry => HOL Theory thry HOLThm
defMULT' = newRecursiveDefinition "*" recursionNUM
    [str| (!n. 0 * n = 0) /\
          (!m n. (SUC m) * n = (m * n) + n) |]


defEXP' :: NumsCtxt thry => HOL Theory thry HOLThm
defEXP' = newRecursiveDefinition "EXP" recursionNUM
    [str| (!m. m EXP 0 = 1) /\
          (!m n. m EXP (SUC n) = m * (m EXP n)) |]


defLE' :: NumsCtxt thry => HOL Theory thry HOLThm
defLE' = newRecursiveDefinition "<=" recursionNUM
    [str| (!m. (m <= 0) <=> (m = 0)) /\
          (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n)) |]


defLT' :: NumsCtxt thry => HOL Theory thry HOLThm
defLT' = newRecursiveDefinition "<" recursionNUM
    [str| (!m. (m < 0) <=> F) /\
          (!m n. (m < SUC n) <=> (m = n) \/ (m < n)) |]


defGE' :: PairCtxt thry => HOL Theory thry HOLThm
defGE' = newDefinition ">="
    [str| m >= n <=> n <= m |]


defGT' :: PairCtxt thry => HOL Theory thry HOLThm
defGT' = newDefinition ">"
    [str| m > n <=> n < m |]


defMAX' :: PairCtxt thry => HOL Theory thry HOLThm
defMAX' = newDefinition "MAX"
    [str| !m n. MAX m n = if m <= n then n else m |]


defMIN' :: PairCtxt thry => HOL Theory thry HOLThm
defMIN' = newDefinition "MIN"
    [str| !m n. MIN m n = if m <= n then m else n |]


defEVEN' :: NumsCtxt thry => HOL Theory thry HOLThm
defEVEN' = newRecursiveDefinition "EVEN" recursionNUM
    [str| (EVEN 0 <=> T) /\
          (!n. EVEN (SUC n) <=> ~(EVEN n)) |]


defODD' :: NumsCtxt thry => HOL Theory thry HOLThm
defODD' = newRecursiveDefinition "ODD" recursionNUM
    [str| (ODD 0 <=> F) /\
          (!n. ODD (SUC n) <=> ~(ODD n)) |]


defSUB' :: NumsCtxt thry => HOL Theory thry HOLThm
defSUB' = newRecursiveDefinition "-" recursionNUM
    [str| (!m. m - 0 = m) /\
          (!m n. m - (SUC n) = PRE(m - n)) |]


defFACT' :: NumsCtxt thry => HOL Theory thry HOLThm
defFACT' = newRecursiveDefinition "FACT" recursionNUM
    [str| (FACT 0 = 1) /\
          (!n. FACT (SUC n) = (SUC n) * FACT(n)) |]
