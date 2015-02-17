module HaskHOL.Lib.Lists.Base where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.IndTypes
import HaskHOL.Lib.Recursion

import HaskHOL.Lib.Lists.A

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



inductLIST' :: (BasicConvs thry, ListsACtxt thry) => HOL cls thry HOLThm
inductLIST' = cacheProof "inductLIST'" ctxtListsA $
    prove [str| !P:(A)list->bool. P [] /\ 
                (!h t. P t ==> P (CONS h t)) ==> !l. P l |] $
      tacMATCH_ACCEPT inductLIST

tacLIST_INDUCT :: (BasicConvs thry, ListsACtxt thry) => Tactic cls thry
tacLIST_INDUCT = 
    tacMATCH_MP inductLIST' `_THEN` tacCONJ `_THENL`
    [ _ALL, tacGEN `_THEN` tacGEN `_THEN` tacDISCH]

thmMONO_ALL :: (BasicConvs thry, ListsACtxt thry) => HOL cls thry HOLThm
thmMONO_ALL = cacheProof "thmMONO_ALL" ctxtListsA .
    prove "(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l" $
      tacDISCH `_THEN` tacSPEC ("l:A list", "l:A list") `_THEN`
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defALL] `_THEN` tacASM_MESON_NIL

thmMONO_ALL2 :: (BasicConvs thry, ListsACtxt thry) => HOL cls thry HOLThm
thmMONO_ALL2 = cacheProof "thmMONO_ALL2" ctxtListsA .
    prove [str| (!x y. (P:A->B->bool) x y ==> Q x y) ==> 
                ALL2 P l l' ==> ALL2 Q l l' |] $
      tacDISCH `_THEN` tacSPEC ("l':B list", "l':B list") `_THEN`
      tacSPEC ("l:A list", "l:A list") `_THEN` tacLIST_INDUCT `_THEN`
      tacREWRITE [defALL2] `_THEN` tacGEN `_THEN` tacCOND_CASES `_THEN`
      tacREWRITE_NIL `_THEN` tacASM_MESON_NIL


