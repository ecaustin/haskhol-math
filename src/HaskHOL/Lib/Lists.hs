{-|
  Module:    HaskHOL.Lib.Lists
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Lists 
    ( ListsCtxt
    , ctxtLists
    , lists
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
    , tacLIST_INDUCT
    , thmMONO_ALL
    , thmMONO_ALL2
    , thmAPPEND_NIL
    , thmAPPEND_ASSOC
    , thmREVERSE_APPEND
    , thmREVERSE_APPEND2
    , mkChar
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Lists.Base
import HaskHOL.Lib.Lists.Context
import HaskHOL.Lib.Lists.PQ

import Data.Char (ord)
import Data.Bits (testBit)

defHD :: ListsACtxt thry => HOL cls thry HOLThm
defHD = cacheProof "defHD" ctxtListsA $ getRecursiveDefinition "HD"

defTL :: ListsACtxt thry => HOL cls thry HOLThm
defTL = cacheProof "defTL" ctxtListsA $ getRecursiveDefinition "TL"

defAPPEND :: ListsACtxt thry => HOL cls thry HOLThm
defAPPEND = cacheProof "defAPPEND" ctxtListsA $ getRecursiveDefinition "APPEND"

defREVERSE :: ListsACtxt thry => HOL cls thry HOLThm
defREVERSE = cacheProof "defREVERSE" ctxtListsA $ 
    getRecursiveDefinition "REVERSE"

defLENGTH :: ListsACtxt thry => HOL cls thry HOLThm
defLENGTH = cacheProof "defLENGTH" ctxtListsA $ getRecursiveDefinition "LENGTH"

defMAP :: ListsACtxt thry => HOL cls thry HOLThm
defMAP = cacheProof "defMAP" ctxtListsA $ getRecursiveDefinition "MAP"

defLAST :: ListsACtxt thry => HOL cls thry HOLThm
defLAST = cacheProof "defLAST" ctxtListsA $ getRecursiveDefinition "LAST"

defBUTLAST :: ListsACtxt thry => HOL cls thry HOLThm
defBUTLAST = cacheProof "defBUTLAST" ctxtListsA $ 
    getRecursiveDefinition "BUTLAST"

defREPLICATE :: ListsACtxt thry => HOL cls thry HOLThm
defREPLICATE = cacheProof "defREPLICATE" ctxtListsA $ 
    getRecursiveDefinition "REPLICATE"

defNULL :: ListsACtxt thry => HOL cls thry HOLThm
defNULL = cacheProof "defNULL" ctxtListsA $ getRecursiveDefinition "NULL"

defALL :: ListsACtxt thry => HOL cls thry HOLThm
defALL = cacheProof "defALL" ctxtListsA $ getRecursiveDefinition "ALL"

defEX :: ListsACtxt thry => HOL cls thry HOLThm
defEX = cacheProof "defEX" ctxtListsA $ getRecursiveDefinition "EX"

defITLIST :: ListsACtxt thry => HOL cls thry HOLThm
defITLIST = cacheProof "defITLIST" ctxtListsA $ getRecursiveDefinition "ITLIST"

defALL2 :: ListsACtxt thry => HOL cls thry HOLThm
defALL2 = cacheProof "defALL2" ctxtListsA $ getRecursiveDefinition "ALL2"

defMAP2 :: ListsACtxt thry => HOL cls thry HOLThm
defMAP2 = cacheProof "defMAP2" ctxtListsA $ getRecursiveDefinition "MAP2"

defEL :: ListsACtxt thry => HOL cls thry HOLThm
defEL = cacheProof "defEL" ctxtListsA $ getRecursiveDefinition "EL"

defFILTER :: ListsACtxt thry => HOL cls thry HOLThm
defFILTER = cacheProof "defFILTER" ctxtListsA $ getRecursiveDefinition "FILTER"

defASSOC :: ListsACtxt thry => HOL cls thry HOLThm
defASSOC = cacheProof "defASSOC" ctxtListsA $ getRecursiveDefinition "ASSOC"

defITLIST2 :: ListsACtxt thry => HOL cls thry HOLThm
defITLIST2 = cacheProof "defITLIST2" ctxtListsA $ 
    getRecursiveDefinition "ITLIST2"

defZIP :: ListsACtxt thry => HOL cls thry HOLThm
defZIP = cacheProof "defZIP" ctxtListsA $ getRecursiveDefinition "ZIP"

defMEM :: ListsACtxt thry => HOL cls thry HOLThm
defMEM = cacheProof "defMEM" ctxtListsA $ getRecursiveDefinition "MEM"


inductCHAR :: ListsACtxt thry => HOL cls thry HOLThm
inductCHAR = cacheProof "inductCHAR" ctxtListsA $
    liftM fst tyChar

recursionCHAR :: ListsACtxt thry => HOL cls thry HOLThm
recursionCHAR = cacheProof "recursionCHAR" ctxtListsA $
    liftM snd tyChar

tyChar :: ListsACtxt thry => HOL cls thry (HOLThm, HOLThm)
tyChar = getType "char"

tacLIST_INDUCT :: ListsCtxt thry => Tactic cls thry
tacLIST_INDUCT = Base.tacLIST_INDUCT

thmMONO_ALL :: ListsCtxt thry => HOL cls thry HOLThm
thmMONO_ALL = Base.thmMON_ALL

thmMONO_ALL2 :: ListsCtxt thry => HOL cls thry HOLThm
thmMONO_ALL2

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
    prove [str| !! 'A. ! (xs:'A list) (ys:'A list). 
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
               
