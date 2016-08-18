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
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.IndTypes

import qualified HaskHOL.Lib.Lists.Base as Base
import HaskHOL.Lib.Lists.Context
import HaskHOL.Lib.Lists.PQ

import Data.Char (ord)
import Data.Bits (testBit)

defHD :: ListsCtxt thry => HOL cls thry HOLThm
defHD = cacheProof "defHD" ctxtLists $ getRecursiveDefinition "HD"

defTL :: ListsCtxt thry => HOL cls thry HOLThm
defTL = cacheProof "defTL" ctxtLists $ getRecursiveDefinition "TL"

defAPPEND :: ListsCtxt thry => HOL cls thry HOLThm
defAPPEND = cacheProof "defAPPEND" ctxtLists $ getRecursiveDefinition "APPEND"

defREVERSE :: ListsCtxt thry => HOL cls thry HOLThm
defREVERSE = cacheProof "defREVERSE" ctxtLists $ 
    getRecursiveDefinition "REVERSE"

defLENGTH :: ListsCtxt thry => HOL cls thry HOLThm
defLENGTH = cacheProof "defLENGTH" ctxtLists $ getRecursiveDefinition "LENGTH"

defMAP :: ListsCtxt thry => HOL cls thry HOLThm
defMAP = cacheProof "defMAP" ctxtLists $ getRecursiveDefinition "MAP"

defLAST :: ListsCtxt thry => HOL cls thry HOLThm
defLAST = cacheProof "defLAST" ctxtLists $ getRecursiveDefinition "LAST"

defBUTLAST :: ListsCtxt thry => HOL cls thry HOLThm
defBUTLAST = cacheProof "defBUTLAST" ctxtLists $ 
    getRecursiveDefinition "BUTLAST"

defREPLICATE :: ListsCtxt thry => HOL cls thry HOLThm
defREPLICATE = cacheProof "defREPLICATE" ctxtLists $ 
    getRecursiveDefinition "REPLICATE"

defNULL :: ListsCtxt thry => HOL cls thry HOLThm
defNULL = cacheProof "defNULL" ctxtLists $ getRecursiveDefinition "NULL"

defALL :: ListsCtxt thry => HOL cls thry HOLThm
defALL = Base.defALL

defEX :: ListsCtxt thry => HOL cls thry HOLThm
defEX = cacheProof "defEX" ctxtLists $ getRecursiveDefinition "EX"

defITLIST :: ListsCtxt thry => HOL cls thry HOLThm
defITLIST = cacheProof "defITLIST" ctxtLists $ getRecursiveDefinition "ITLIST"

defALL2 :: ListsCtxt thry => HOL cls thry HOLThm
defALL2 = Base.defALL2

defMAP2 :: ListsCtxt thry => HOL cls thry HOLThm
defMAP2 = cacheProof "defMAP2" ctxtLists $ getRecursiveDefinition "MAP2"

defEL :: ListsCtxt thry => HOL cls thry HOLThm
defEL = cacheProof "defEL" ctxtLists $ getRecursiveDefinition "EL"

defFILTER :: ListsCtxt thry => HOL cls thry HOLThm
defFILTER = cacheProof "defFILTER" ctxtLists $ getRecursiveDefinition "FILTER"

defASSOC :: ListsCtxt thry => HOL cls thry HOLThm
defASSOC = cacheProof "defASSOC" ctxtLists $ getRecursiveDefinition "ASSOC"

defITLIST2 :: ListsCtxt thry => HOL cls thry HOLThm
defITLIST2 = cacheProof "defITLIST2" ctxtLists $ 
    getRecursiveDefinition "ITLIST2"

defZIP :: ListsCtxt thry => HOL cls thry HOLThm
defZIP = cacheProof "defZIP" ctxtLists $ getRecursiveDefinition "ZIP"

defMEM :: ListsCtxt thry => HOL cls thry HOLThm
defMEM = cacheProof "defMEM" ctxtLists $ getRecursiveDefinition "MEM"


inductCHAR :: ListsCtxt thry => HOL cls thry HOLThm
inductCHAR = cacheProof "inductCHAR" ctxtLists $
    liftM fst tyChar

recursionCHAR :: ListsCtxt thry => HOL cls thry HOLThm
recursionCHAR = cacheProof "recursionCHAR" ctxtLists $
    liftM snd tyChar

tyChar :: ListsCtxt thry => HOL cls thry (HOLThm, HOLThm)
tyChar = getType "char"

tacLIST_INDUCT :: ListsCtxt thry => Tactic cls thry
tacLIST_INDUCT = Base.tacLIST_INDUCT

thmMONO_ALL :: ListsCtxt thry => HOL cls thry HOLThm
thmMONO_ALL = Base.thmMONO_ALL

thmMONO_ALL2 :: ListsCtxt thry => HOL cls thry HOLThm
thmMONO_ALL2 = Base.thmMONO_ALL2

thmAPPEND_NIL :: ListsCtxt thry => HOL cls thry HOLThm
thmAPPEND_NIL = cacheProof "thmAPPEND_NIL" ctxtLists .
    prove [txt| ! (l:A list). APPEND l [] = l |] $
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defAPPEND]

thmAPPEND_ASSOC :: ListsCtxt thry => HOL cls thry HOLThm
thmAPPEND_ASSOC = cacheProof "thmAPPEND_ASSOC" ctxtLists .
    prove [txt| ! (l:A list) m n. APPEND l (APPEND m n) = 
                                  APPEND (APPEND l m) n |] $
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defAPPEND]

thmREVERSE_APPEND :: ListsCtxt thry => HOL cls thry HOLThm
thmREVERSE_APPEND = cacheProof "thmREVERSE_APPEND" ctxtLists .
    prove [txt| ! (xs:A list) (ys:A list). REVERSE (APPEND xs ys) = 
                                           APPEND (REVERSE ys) (REVERSE xs) |] $
      tacLIST_INDUCT `_THEN` 
      tacASM_REWRITE [defAPPEND, defREVERSE, thmAPPEND_NIL, thmAPPEND_ASSOC]

thmREVERSE_APPEND2 :: ListsCtxt thry => HOL cls thry HOLThm
thmREVERSE_APPEND2 = cacheProof "thmREVERSE_APPEND2" ctxtLists .
    prove [txt| !! 'A. ! (xs:'A list) (ys:'A list). 
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
               foldrM (flip mkComb) ascii bits
        
        mkBool :: ListsCtxt thry => Bool -> HOL cls thry HOLTerm
        mkBool True = serve tmT
        mkBool _ = serve tmF
               
