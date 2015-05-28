{-# LANGUAGE ConstraintKinds, QuasiQuotes #-}
module HaskHOL.Lib.Lists.A.Base where

import HaskHOL.Core

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.IndTypes 

defHD' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defHD' = newRecursiveDefinition "HD" recursionLIST "HD(CONS (h:A) t) = h"

defTL' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defTL' = newRecursiveDefinition "TL" recursionLIST "TL(CONS (h:A) t) = t"

defAPPEND' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defAPPEND' = newRecursiveDefinition "APPEND" recursionLIST
    [str| (!l:(A)list. APPEND [] l = l) /\
          (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l)) |]

defREVERSE' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defREVERSE' = newRecursiveDefinition "REVERSE" recursionLIST
    [str| (REVERSE [] = []) /\
          (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x]) |]

defLENGTH' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defLENGTH' = newRecursiveDefinition "LENGTH" recursionLIST
    [str| (LENGTH [] = 0) /\
          (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t)) |]

defMAP' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defMAP' = newRecursiveDefinition "MAP" recursionLIST
    [str| (!f:A->B. MAP f NIL = NIL) /\
          (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t)) |]

defLAST' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defLAST' = newRecursiveDefinition "LAST" recursionLIST 
    "LAST (CONS (h:A) t) = if t = [] then h else LAST t"

defBUTLAST' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defBUTLAST' = newRecursiveDefinition "BUTLAST" recursionLIST
    [str| (BUTLAST [] = []) /\
          (BUTLAST (CONS h t) = if t = [] then [] else CONS h (BUTLAST t)) |]

defREPLICATE' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defREPLICATE' = newRecursiveDefinition "REPLICATE" recursionNUM
    [str| (REPLICATE 0 x = []) /\
          (REPLICATE (SUC n) x = CONS x (REPLICATE n x)) |]

defNULL' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defNULL' = newRecursiveDefinition "NULL" recursionLIST
    [str| (NULL [] = T) /\
          (NULL (CONS h t) = F) |]

defALL' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defALL' = newRecursiveDefinition "ALL" recursionLIST
    [str| (ALL P [] = T) /\
          (ALL P (CONS h t) <=> P h /\ ALL P t) |]

defEX' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defEX' = newRecursiveDefinition "EX" recursionLIST
    [str| (EX P [] = F) /\
          (EX P (CONS h t) <=> P h \/ EX P t) |]

defITLIST' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defITLIST' = newRecursiveDefinition "ITLIST" recursionLIST
    [str| (ITLIST f [] b = b) /\
          (ITLIST f (CONS h t) b = f h (ITLIST f t b)) |]

defMEM' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defMEM' = newRecursiveDefinition "MEM" recursionLIST
    [str| (MEM x [] <=> F) /\
          (MEM x (CONS h t) <=> (x = h) \/ MEM x t) |]

defALL2' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defALL2' = newRecursiveDefinition "ALL2" recursionLIST
    [str| (ALL2 P [] l2 <=> (l2 = [])) /\
          (ALL2 P (CONS h1 t1) l2 <=>
           if l2 = [] then F
           else P h1 (HD l2) /\ ALL2 P t1 (TL l2)) |]

defMAP2' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defMAP2' = newRecursiveDefinition "MAP2" recursionLIST
    [str| (MAP2 f [] l = []) /\
          (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l))) |]

defEL' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defEL' = newRecursiveDefinition "EL" recursionNUM
    [str| (EL 0 l = HD l) /\
          (EL (SUC n) l = EL n (TL l)) |]

defFILTER' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defFILTER' = newRecursiveDefinition "FILTER" recursionLIST
    [str| (FILTER P [] = []) /\
          (FILTER P (CONS h t) = 
           if P h then CONS h (FILTER P t) else FILTER P t) |]

defASSOC' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defASSOC' = newRecursiveDefinition "ASSOC" recursionLIST
    "ASSOC a (CONS h t) = if FST h = a then SND h else ASSOC a t"

defITLIST2' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defITLIST2' = newRecursiveDefinition "ITLIST2" recursionLIST
    [str| (ITLIST2 f [] l2 b = b) /\
          (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b)) 
    |]

defZIP' :: IndTypesCtxt thry => HOL Theory thry HOLThm
defZIP' = newRecursiveDefinition "ZIP" recursionLIST
    [str| (ZIP [] l2 = []) /\
          (ZIP (CONS h1 t1) l2 = CONS (h1,HD l2) (ZIP t1 (TL l2))) |]

{-
defCONCAT_MAP' :: HOL Theory thry HOLThm
defCONCAT_MAP' = newDefinition "CONCAT_MAP"
    [str| CONCAT_MAP f xs = ITLIST (APPEND o f) xs [] |]
-}

tyDefCHAR' :: IndTypesCtxt thry
           => HOL Theory thry (HOLThm, HOLThm)
tyDefCHAR' = defineType "char = ASCII bool bool bool bool bool bool bool bool"
