{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.IndTypesPre.Context
    ( IndTypesPreType
    , IndTypesPreThry
    , IndTypesPreCtxt
    , ctxtIndTypesPre
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition, newSpecification)

import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Pair

import HaskHOL.Lib.IndTypesPre.Base

import HaskHOL.Lib.WF.Context

data IndTypesPreThry
type instance IndTypesPreThry == IndTypesPreThry = 'True

instance CtxtName IndTypesPreThry where
    ctxtName _ = "IndTypesPreCtxt"

type instance PolyTheory IndTypesPreType b = IndTypesPreCtxt b

type family IndTypesPreCtxt a :: Constraint where
    IndTypesPreCtxt a = (Typeable a, WFCtxt a, IndTypesPreContext a ~ 'True)

type IndTypesPreType = ExtThry IndTypesPreThry WFType

type family IndTypesPreContext a :: Bool where
    IndTypesPreContext UnsafeThry = 'True
    IndTypesPreContext BaseThry = 'False
    IndTypesPreContext (ExtThry a b) = IndTypesPreContext b || (a == IndTypesPreThry)

ctxtIndTypesPre :: TheoryPath IndTypesPreType
ctxtIndTypesPre = extendTheory ctxtWF $(thisModule') $
    do void $ newSpecification ["NUMFST", "NUMSND"] =<<
                ruleMATCH_MP thmINJ_INVERSE2 thmNUMPAIR_INJ
       void $ newSpecification ["NUMLEFT", "NUMRIGHT"] =<<
                ruleMATCH_MP thmINJ_INVERSE2 thmNUMSUM_INJ
       mapM_ newDefinition
         [ ("INJN", [txt| INJN (m:num) = \(n:num) (a:A). n = m |])
         , ("INJA", [txt| INJA (a:A) = \(n:num) b. b = a |])
         , ("INJF", [txt| INJF (f:num->(num->A->bool)) = 
                            \n. f (NUMFST n) (NUMSND n) |])
         , ("INJP", [txt| INJP f1 f2:num->A->bool =
                            \n a. if NUMLEFT n then f1 (NUMRIGHT n) a 
                                  else f2 (NUMRIGHT n) a |])
         , ("ZCONSTR", [txt| ZCONSTR c i r :num->A->bool = 
                               INJP (INJN (SUC c)) (INJP (INJA i) (INJF r)) |])
         , ("ZBOT", [txt| ZBOT = INJP (INJN 0) (@z:num->A->bool. T) |])
         ]
       (rep, _, _) <- newInductiveDefinition "ZRECSPACE"
                        [txt| ZRECSPACE (ZBOT:num->A->bool) /\
                              (!c i r. (!n. ZRECSPACE (r n)) ==> 
                                            ZRECSPACE (ZCONSTR c i r)) |]
       void $ newBasicTypeDefinition "recspace" "_mk_rec" "_dest_rec" =<< 
                ruleCONJUNCT1 rep
       mapM_ newDefinition
         [ ("BOTTOM", [txt| BOTTOM = _mk_rec (ZBOT:num->A->bool) |])
         , ("CONSTR", [txt| CONSTR c i r :(A)recspace = 
                              _mk_rec (ZCONSTR c i (\n. _dest_rec(r n))) |])
         , ("FNIL", [txt| FNIL (n:num) = @x:A. T |])
         ]
       void $ newRecursiveDefinition recursionNUM
                ("FCONS", [txt| (!a f. FCONS (a:A) f 0 = a) /\ 
                                (!a f n. FCONS (a:A) f (SUC n) = f n) |])
