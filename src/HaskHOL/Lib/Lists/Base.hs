module HaskHOL.Lib.Lists.Base where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.IndTypes
import HaskHOL.Lib.Recursion

tacLIST_INDUCT :: IndTypesCtxt thry => Tactic cls thry
tacLIST_INDUCT = 
    tacMATCH_MP inductLIST' `_THEN` tacCONJ `_THENL`
    [ _ALL, tacGEN `_THEN` tacGEN `_THEN` tacDISCH]
  where inductLIST' :: IndTypesCtxt thry => HOL cls thry HOLThm
        inductLIST' = unsafeCacheProof "inductLIST'" $
          prove [txt| !P:(A)list->bool. P [] /\ 
                      (!h t. P t ==> P (CONS h t)) ==> !l. P l |] $
            tacMATCH_ACCEPT inductLIST

defALL :: HOL cls thry HOLThm
defALL = unsafeCacheProof "defALL" $ getRecursiveDefinition "ALL"

defALL2 :: HOL cls thry HOLThm
defALL2 = unsafeCacheProof "defALL2" $ getRecursiveDefinition "ALL2"

thmMONO_ALL :: IndTypesCtxt thry => HOL cls thry HOLThm
thmMONO_ALL = unsafeCacheProof "thmMONO_ALL" .
    prove [txt| (!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l |] $
      tacDISCH `_THEN` tacSPEC ([txt| l:A list |], [txt| l:A list |]) `_THEN`
      tacLIST_INDUCT `_THEN` tacASM_REWRITE [defALL] `_THEN` tacASM_MESON_NIL

thmMONO_ALL2 :: IndTypesCtxt thry => HOL cls thry HOLThm
thmMONO_ALL2 = unsafeCacheProof "thmMONO_ALL2" .
    prove [txt| (!x y. (P:A->B->bool) x y ==> Q x y) ==> 
                ALL2 P l l' ==> ALL2 Q l l' |] $
      tacDISCH `_THEN` tacSPEC ([txt| l':B list |], [txt| l':B list |]) `_THEN`
      tacSPEC ([txt| l:A list |], [txt| l:A list |]) `_THEN` 
      tacLIST_INDUCT `_THEN`
      tacREWRITE [defALL2] `_THEN` tacGEN `_THEN` tacCOND_CASES `_THEN`
      tacREWRITE_NIL `_THEN` tacASM_MESON_NIL


