module HaskHOL.Lib.IndTypes.A.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification,
                                 newSpecification, newDefinition)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Recursion
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Arith
import HaskHOL.Lib.CalcNum
import HaskHOL.Lib.WF
import HaskHOL.Lib.WF.Context

import HaskHOL.Lib.IndTypes.A.Pre

thmNUMPAIR_INJ :: (BasicConvs thry, WFCtxt thry) => HOL cls thry HOLThm
thmNUMPAIR_INJ = cacheProof "thmNUMPAIR_INJ" ctxtWF $
    prove [str| !x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> 
                              (x1 = x2) /\ (y1 = y2) |] $
      _REPEAT tacGEN `_THEN` tacEQ `_THEN` tacDISCH `_THEN` 
      tacASM_REWRITE_NIL `_THEN`
      _FIRST_ASSUM (tacSUBST_ALL . ruleMATCH_MP thmNUMPAIR_INJ_LEMMA) `_THEN`
      _POP_ASSUM tacMP `_THEN` tacREWRITE [defNUMPAIR] `_THEN`
      tacREWRITE [thmEQ_MULT_LCANCEL, thmEQ_ADD_RCANCEL, thmEXP_EQ_0, thmARITH]

specNUMPAIR_DEST' :: (BasicConvs thry, WFCtxt thry) => HOL Theory thry HOLThm
specNUMPAIR_DEST' = newSpecification ["NUMFST", "NUMSND"] =<<
    ruleMATCH_MP thmINJ_INVERSE2 thmNUMPAIR_INJ

specNUMSUM_DEST' :: (BasicConvs thry, WFCtxt thry) => HOL Theory thry HOLThm
specNUMSUM_DEST' = newSpecification ["NUMLEFT", "NUMRIGHT"] =<<
    ruleMATCH_MP thmINJ_INVERSE2 thmNUMSUM_INJ


defINJN' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defINJN' = newDefinition "INJN"
    [str| INJN (m:num) = \(n:num) (a:A). n = m |]

defINJA' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defINJA' = newDefinition "INJA"
    [str| INJA (a:A) = \(n:num) b. b = a |]

defINJF' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defINJF' = newDefinition "INJF"
    [str| INJF (f:num->(num->A->bool)) = \n. f (NUMFST n) (NUMSND n) |]

defINJP' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defINJP' = newDefinition "INJP"
    [str| INJP f1 f2:num->A->bool =
              \n a. if NUMLEFT n then f1 (NUMRIGHT n) a 
                    else f2 (NUMRIGHT n) a |]
           

defZCONSTR' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defZCONSTR' = newDefinition "ZCONSTR"
    [str| ZCONSTR c i r :num->A->bool = 
              INJP (INJN (SUC c)) (INJP (INJA i) (INJF r)) |]

defZBOT' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defZBOT' = newDefinition "ZBOT"
    [str| ZBOT = INJP (INJN 0) (@z:num->A->bool. T) |]

indDefZRECSPACE' :: (BasicConvs thry, IndDefsCtxt thry) 
                 => HOL Theory thry (HOLThm, HOLThm, HOLThm)
indDefZRECSPACE' = newInductiveDefinition "ZRECSPACE"
    [str| ZRECSPACE (ZBOT:num->A->bool) /\
          (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r)) |]

tyDefRecspace' :: BoolCtxt thry => HOLThm -> HOL Theory thry (HOLThm, HOLThm)
tyDefRecspace' rep =
    newBasicTypeDefinition "recspace" "_mk_rec" "_dest_rec" =<< 
      ruleCONJUNCT1 rep

defBOTTOM' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defBOTTOM' = newDefinition "BOTTOM"
    [str| BOTTOM = _mk_rec (ZBOT:num->A->bool) |]

defCONSTR' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defCONSTR' = newDefinition "CONSTR"
    [str| CONSTR c i r :(A)recspace = 
              _mk_rec (ZCONSTR c i (\n. _dest_rec(r n))) |]

defFCONS' :: (BasicConvs thry, NumsCtxt thry) => HOL Theory thry HOLThm
defFCONS' = newRecursiveDefinition "FCONS" recursionNUM
    [str| (!a f. FCONS (a:A) f 0 = a) /\ 
          (!a f n. FCONS (a:A) f (SUC n) = f n) |]

defFNIL' :: (BasicConvs thry, PairCtxt thry) => HOL Theory thry HOLThm
defFNIL' = newDefinition "FNIL"
    "FNIL (n:num) = @x:A. T"
