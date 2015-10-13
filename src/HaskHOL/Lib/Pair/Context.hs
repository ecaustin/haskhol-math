{-# LANGUAGE DataKinds, EmptyDataDecls, TypeOperators, UndecidableInstances #-}
module HaskHOL.Lib.Pair.Context
    ( PairType
    , PairThry
    , PairCtxt
    , ctxtPair
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (newDefinition)
import qualified HaskHOL.Deductive as D (newDefinition)

import HaskHOL.Lib.Pair.Base

data PairThry
type instance PairThry == PairThry = 'True

instance CtxtName PairThry where
    ctxtName _ = "PairCtxt"

type instance PolyTheory PairType b = PairCtxt b

type family PairCtxt a :: Constraint where
    PairCtxt a = (Typeable a, DeductiveCtxt a, PairContext a ~ 'True)

type PairType = ExtThry PairThry DeductiveType

type family PairContext a :: Bool where
    PairContext BaseThry = 'False
    PairContext (ExtThry a b) = PairContext b || (a == PairThry)

ctxtPair :: TheoryPath PairType
ctxtPair = extendTheory ctxtDeductive $(thisModule') $
-- stage1
    do defs1 <- mapM D.newDefinition 
                  [ ("LET", [str| LET (f:A->B) x = f x |])
                  , ("LET_END", [str| LET_END (t:A) = t |])
                  , ("GABS", [str| GABS (P:A->bool) = (@) P |])
                  , ("GEQ", [str| GEQ a b = (a:A = b) |])
                  , ("mk_pair", [str| mk_pair (x:A) (y:B) = \ a b. (a = x) /\ 
                                                                   (b = y) |])
                  ]
       mapM_ D.newDefinition
         [ ("_SEQPATTERN", [str| _SEQPATTERN = \ r s x. if ? y. r x y 
                                                        then r x else s x |])
         , ("_UNGUARDED_PATTERN", [str| _UNGUARDED_PATTERN = \ p r. p /\ r |])
         , ("_GUARDED_PATTERN",[str| _GUARDED_PATTERN = \ p g r. p /\ g /\ r |])
         , ("_MATCH", [str| _MATCH =  \ e r. if (?!) (r e) 
                                             then (@) (r e) else @ z. F |])
         , ("_FUNCTION", [str| _FUNCTION = \ r x. if (?!) (r x) 
                                                  then (@) (r x) else @ z. F |])
         ]
-- stage2
       void $ newTypeDefinition "prod" "ABS_prod" "REP_prod" thmPAIR_EXISTS
       parseAsInfix (",", (14, "right"))
       defs2 <- mapM D.newDefinition
                  [ (",", [str| ((x:A), (y:B)) = ABS_prod(mk_pair x y) |])
                  , ("FST", [str| FST (p:A#B) = @ x. ? y. p = (x, y) |])
                  , ("SND", [str| SND (p:A#B) = @ y. ? x. p = (x, y) |])
                  ]
-- stage3
       extendBasicRewrites [thmFST, thmSND, thmPAIR]
       defs3 <- sequence [ def_one, defI, defO, defCOND, def_FALSITY_
                         , defTY_EXISTS, defTY_FORALL
                         , defEXISTS_UNIQUE, defEXISTS, defFORALL
                         , defNOT, defOR, defIMP, defAND
                         , defFALSE, defT
                         ]
       let ths' = zip [ "LET", "LET_END", "GABS", "GEQ", "mk_pair"
                      , ",", "FST", "SND"
                      , "one", "I", "o", "COND", "_FALSITY_"
                      , "??", "!!", "?!", "?", "!", "~", "\\/", "==>", "/\\"
                      , "F", "T"
                      ] $ defs1 ++ defs2 ++ defs3
       acid <- openLocalStateHOL (Definitions mapEmpty)
       updateHOL acid (AddDefinitions ths')
       closeAcidStateHOL acid
       mapM_ newDefinition
         [ ("CURRY", [str| CURRY(f:A#B->C) x y = f(x,y) |])
         , ("UNCURRY", [str| !f x y. UNCURRY(f:A->B->C)(x,y) = f x y |])
         , ("PASSOC", [str| !f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = 
                                      f ((x,y),z) |])
         ]
-- stage4
       addIndDef ("prod", (1, inductPAIR, recursionPAIR))
       extendBasicConvs [("convGEN_BETA", 
                          ([str| GABS (\ a. b) c |], "HaskHOL.Lib.Pair"))]
