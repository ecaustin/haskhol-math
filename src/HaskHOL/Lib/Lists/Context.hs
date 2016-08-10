{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Lists.Context
    ( ListsType
    , ListsThry
    , ListsCtxt
    , ctxtLists
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition)

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypes.Context

import HaskHOL.Lib.Lists.Pre
import HaskHOL.Lib.Lists.Base


data ListsThry
type instance ListsThry == ListsThry = 'True

instance CtxtName ListsThry where
    ctxtName _ = "ListsCtxt"

type instance PolyTheory ListsType b = ListsCtxt b

type family ListsCtxt a :: Constraint where
    ListsCtxt a = (Typeable a, IndTypesCtxt a, ListsContext a ~ 'True)

type ListsType = ExtThry ListsThry IndTypesType

type family ListsContext a :: Bool where
    ListsContext BaseThry = 'False
    ListsContext (ExtThry a b) = ListsContext b || (a == ListsThry)

ctxtLists :: TheoryPath ListsType
ctxtLists = extendTheory ctxtIndTypes $(thisModule') $
    do mapM_ (newRecursiveDefinition recursionLIST) 
         [ ("HD", [txt| HD(CONS (h:A) t) = h |])
         , ("TL", [txt| TL(CONS (h:A) t) = t |])
         , ("APPEND",
            [txt| (!l:(A)list. APPEND [] l = l) /\
                  (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l)) |])
         , ("REVERSE", 
            [txt| (REVERSE [] = []) /\
                  (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x]) |])
         , ("LENGTH", 
            [txt| (LENGTH [] = 0) /\
                  (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t)) |])
         , ("MAP", 
            [txt| (!f:A->B. MAP f NIL = NIL) /\
                  (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t)) |])
         , ("LAST", 
            [txt| LAST (CONS (h:A) t) = if t = [] then h else LAST t |])
         , ("BUTLAST", 
            [txt| (BUTLAST [] = []) /\
                  (BUTLAST (CONS h t) = if t = [] then [] 
                                        else CONS h (BUTLAST t)) |])
         , ("NULL", 
            [txt| (NULL [] = T) /\
                  (NULL (CONS h t) = F) |])
         , ("ALL", 
            [txt| (ALL P [] = T) /\
                  (ALL P (CONS h t) <=> P h /\ ALL P t) |])
         , ("EX", 
            [txt| (EX P [] = F) /\
                  (EX P (CONS h t) <=> P h \/ EX P t) |])
         , ("ITLIST", 
            [txt| (ITLIST f [] b = b) /\
                  (ITLIST f (CONS h t) b = f h (ITLIST f t b)) |])
         , ("MEM", 
            [txt| (MEM x [] <=> F) /\
                  (MEM x (CONS h t) <=> (x = h) \/ MEM x t) |])
         , ("ALL2", 
            [txt| (ALL2 P [] l2 <=> (l2 = [])) /\
                  (ALL2 P (CONS h1 t1) l2 <=>
                      if l2 = [] then F
                      else P h1 (HD l2) /\ ALL2 P t1 (TL l2)) |])
         , ("MAP2", 
            [txt| (MAP2 f [] l = []) /\
                  (MAP2 f (CONS h1 t1) l = 
                      CONS (f h1 (HD l)) (MAP2 f t1 (TL l))) |])
         , ("FILTER", 
            [txt| (FILTER P [] = []) /\
                  (FILTER P (CONS h t) = 
                      if P h then CONS h (FILTER P t) else FILTER P t) |])
         , ("ASSOC", 
            [txt| ASSOC a (CONS h t) = 
                      if FST h = a then SND h else ASSOC a t |])
         , ("ITLIST2", 
            [txt| (ITLIST2 f [] l2 b = b) /\
                  (ITLIST2 f (CONS h1 t1) l2 b = 
                      f h1 (HD l2) (ITLIST2 f t1 (TL l2) b)) |])
         , ("ZIP", 
            [txt| (ZIP [] l2 = []) /\
                  (ZIP (CONS h1 t1) l2 = CONS (h1,HD l2) (ZIP t1 (TL l2))) |])
         ]
       mapM_ (newRecursiveDefinition recursionNUM)
         [ ("REPLICATE", 
            [txt| (REPLICATE 0 x = []) /\
                  (REPLICATE (SUC n) x = CONS x (REPLICATE n x)) |])
         , ("EL", 
            [txt| (EL 0 l = HD l) /\
                  (EL (SUC n) l = EL n (TL l)) |])
         ]
       void $ newDefinition ("CONCAT_MAP",
                [txt| CONCAT_MAP f xs = ITLIST (APPEND o f) xs [] |])
       void $ defineType "char = ASCII bool bool bool bool bool bool bool bool"
       newTypeAbbrev "string" "char list"
       mapM_ addMonoThm [thmMONO_ALL, thmMONO_ALL2]
