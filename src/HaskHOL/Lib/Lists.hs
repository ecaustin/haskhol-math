{-|
  Module:    HaskHOL.Lib.Lists
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Lists 
    ( ListsType
    , ListsAThry
    , ListsThry
    , ListsCtxt
    , ctxtLists
    , defHD
    , defTL
    , defAPPEND
    , defREVERSE
    , defLENGTH
    , defMAP
    , defLAST
    , defBUTLAST
    , defREPLICATE
    , defNULL
    , defALL
    , defEX
    , defITLIST
    , defMEM
    , defALL2
    , defMAP2
    , defEL
    , defFILTER
    , defASSOC
    , defITLIST2
    , defZIP
    , inductCHAR
    , recursionCHAR
    , thmMONO_ALL
    , thmMONO_ALL2
    , thmREVERSE_APPEND
    , thmREVERSE_APPEND2
    , mkChar
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Lists.A
import HaskHOL.Lib.Lists.Base
import HaskHOL.Lib.Lists.Context

import Data.Char (ord)
import Data.Bits (testBit)

thmAPPEND_NIL :: ListsCtxt thry => HOL cls thry HOLThm
thmAPPEND_NIL = cacheProof "thmAPPEND_NIL" ctxtLists .
    prove [str| ! (l:A list). APPEND l [] = l |] $
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defAPPEND]

thmAPPEND_ASSOC :: ListsCtxt thry => HOL cls thry HOLThm
thmAPPEND_ASSOC = cacheProof "thmAPPEND_ASSOC" ctxtLists .
    prove [str| ! (l:A list) m n. APPEND l (APPEND m n) = 
                                  APPEND (APPEND l m) n |] $
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defAPPEND]

thmREVERSE_APPEND :: ListsCtxt thry => HOL cls thry HOLThm
thmREVERSE_APPEND = cacheProof "thmREVERSE_APPEND" ctxtLists .
    prove [str| ! (xs:A list) (ys:A list). REVERSE (APPEND xs ys) = 
                                           APPEND (REVERSE ys) (REVERSE xs) |] $
      tacLIST_INDUCT `_THEN` 
      tacASM_REWRITE [defAPPEND, defREVERSE, thmAPPEND_NIL, thmAPPEND_ASSOC]

thmREVERSE_APPEND2 :: ListsCtxt thry => HOL cls thry HOLThm
thmREVERSE_APPEND2 = cacheProof "thmREVERSE_APPEND2" ctxtLists .
    prove [str| !! 'A. ! (xs:A' list) (ys:A' list). 
                REVERSE (APPEND xs ys) = APPEND (REVERSE ys) (REVERSE xs) |] $
      tacGEN_TY `_THEN` tacLIST_INDUCT `_THEN` 
      tacASM_REWRITE [defAPPEND, defREVERSE, thmAPPEND_NIL, thmAPPEND_ASSOC]

{-# INLINEABLE tmASCII #-}
tmASCII :: ListsCtxt thry => PTerm thry
tmASCII = [lists| ASCII |]

{-# INLINEABLE tmT #-}
tmT :: ListsCtxt thry => PTerm thry
tmT = [lists| T |]

{-# INLINEABLE tmF #-}
tmF :: ListsCtxt thry => PTerm thry
tmF = [lists| F |]

mkChar :: ListsCtxt thry => Char -> HOL cls thry HOLTerm
mkChar = mkCode . ord
  where mkCode :: ListsCtxt thry => Int -> HOL cls thry HOLTerm
        mkCode n =
            do ascii <- serve tmASCII
               bits <- mapM (\ i -> mkBool (testBit n i)) [0..7]
               liftO $ foldrM (flip mkComb) ascii bits
        
        mkBool :: ListsCtxt thry => Bool -> HOL cls thry HOLTerm
        mkBool True = serve tmT
        mkBool _ = serve tmF
               
