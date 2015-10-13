{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.IndTypes.Context
    ( IndTypesType
    , IndTypesThry
    , IndTypesCtxt
    , ctxtIndTypes
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newSpecification, newDefinition)
import HaskHOL.Lib.Pair
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums

import HaskHOL.Lib.WF.Context

import HaskHOL.Lib.IndTypes.Pre
import HaskHOL.Lib.IndTypes.Base


data IndTypesThry
type instance IndTypesThry == IndTypesThry = 'True

instance CtxtName IndTypesThry where
    ctxtName _ = "IndTypesCtxt"

type instance PolyTheory IndTypesType b = IndTypesCtxt b

type family IndTypesCtxt a :: Constraint where
    IndTypesCtxt a = (Typeable a, WFCtxt a, IndTypesContext a ~ 'True)

type IndTypesType = ExtThry IndTypesThry WFType

type family IndTypesContext a :: Bool where
    IndTypesContext BaseThry = 'False
    IndTypesContext (ExtThry a b) = IndTypesContext b || (a == IndTypesThry)

ctxtIndTypes :: TheoryPath IndTypesType
ctxtIndTypes = extendTheory ctxtWF $(thisModule') $
-- Stage 1
    do void $ newSpecification ["NUMFST", "NUMSND"] =<<
                ruleMATCH_MP thmINJ_INVERSE2 thmNUMPAIR_INJ
       void $ newSpecification ["NUMLEFT", "NUMRIGHT"] =<<
                ruleMATCH_MP thmINJ_INVERSE2 thmNUMSUM_INJ
       mapM_ newDefinition
         [ ("INJN", [str| INJN (m:num) = \(n:num) (a:A). n = m |])
         , ("INJA", [str| INJA (a:A) = \(n:num) b. b = a |])
         , ("INJF", [str| INJF (f:num->(num->A->bool)) = 
                            \n. f (NUMFST n) (NUMSND n) |])
         , ("INJP", [str| INJP f1 f2:num->A->bool =
                            \n a. if NUMLEFT n then f1 (NUMRIGHT n) a 
                                  else f2 (NUMRIGHT n) a |])
         , ("ZCONSTR", [str| ZCONSTR c i r :num->A->bool = 
                               INJP (INJN (SUC c)) (INJP (INJA i) (INJF r)) |])
         , ("ZBOT", [str| ZBOT = INJP (INJN 0) (@z:num->A->bool. T) |])
         ]
       (rep, _, _) <- newInductiveDefinition "ZRECSPACE"
                        [str| ZRECSPACE (ZBOT:num->A->bool) /\
                              (!c i r. (!n. ZRECSPACE (r n)) ==> 
                                            ZRECSPACE (ZCONSTR c i r)) |]
       void $ newBasicTypeDefinition "recspace" "_mk_rec" "_dest_rec" =<< 
                ruleCONJUNCT1 rep
       mapM_ newDefinition
         [ ("BOTTOM", [str| BOTTOM = _mk_rec (ZBOT:num->A->bool) |])
         , ("CONSTR", [str| CONSTR c i r :(A)recspace = 
                              _mk_rec (ZCONSTR c i (\n. _dest_rec(r n))) |])
         , ("FNIL", [str| FNIL (n:num) = @x:A. T |])
         ]
       void $ newRecursiveDefinition recursionNUM
                ("FCONS", [str| (!a f. FCONS (a:A) f 0 = a) /\ 
                                (!a f n. FCONS (a:A) f (SUC n) = f n) |])
{-
-- Stage 2
       ctxt <- parseContext
       th <- thmCONSTR_REC
       let indDefFun = (defineTypeRaw th) <#< 
                       (parseInductiveTypeSpecification ctxt)
       (sindth, srecth) <- indDefFun "sum = INL A | INR B"
       mapM_ (newRecursiveDefinition srecth)
         [ ("OUTL", [str| OUTL (INL x :A+B) = x |])
         , ("OUTR", [str| OUTR (INR y :A+B) = y |])
         ]
       addIndDef ("sum", (2, sindth, srecth))
-- Stage3
       (oindth, orecth) <- indDefFun "option = NONE | SOME A"
       (lindth, lrecth) <- indDefFun "list = NIL | CONS A list"
       mapM_ addIndDef [ ("option", (2, oindth, orecth))
                       , ("list", (2, lindth, lrecth))
                       ]
       void $ newDefinition 
                ("ISO", [str| ISO (f:A->B) (g:B->A) <=> 
                                (!x. f(g x) = x) /\ (!y. g(f y) = y) |])
       acid1 <- openLocalStateHOL (InductiveTypes mapEmpty)
       updateHOL acid1 (PutInductiveTypes $ mapFromList
         [ ("list = NIL | CONS A list", (lindth, lrecth))
         , ("option = NONE | SOME A", (oindth, orecth))
         , ("sum = INL A | INR B", (sindth, srecth))
         ])
       createCheckpointAndCloseHOL acid1
       boolth <- ruleTAUT "(T <=> F) <=> F"
       acid2 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid2 (PutDistinctnessStore [("bool", boolth)])
       createCheckpointAndCloseHOL acid2
       mapM_ extendRectypeNet =<< liftM mapToAscList getIndDefs
       extendBasicConvs 
                [ ("convMATCH_SEQPATTERN_TRIV", 
                   ("_MATCH x (_SEQPATTERN r s)", "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_SEQPATTERN_TRIV", 
                   ("_FUNCTION (_SEQPATTERN r s) x", "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_ONEPATTERN_TRIV", 
                   ([str| _MATCH x (\y z. P y z) |], "HaskHOL.Lib.IndTypes"))
                , ("convMATCH_ONEPATTERN_TRIV", 
                   ([str|_FUNCTION (\y z. P y z) x|], "HaskHOL.Lib.IndTypes"))
                ]
-}
