{-|
  Module:    HaskHOL.Lib.Arith
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Arith 
    ( ArithCtxt
    , ctxtArith
    , arith
    , defPRE
    , defADD
    , defMULT
    , defEXP
    , defLE
    , defLT
    , defGE
    , defGT
    , defMAX
    , defMIN
    , defEVEN
    , defODD
    , defSUB
    , defFACT
    , thmADD_0
    , thmADD_SUC
    , thmLE_SUC_LT
    , thmLT_SUC_LE
    , thmLE_0
    , wfNUM_PRIM
    , thmSUB_0
    , thmSUB_PRESUC
    , thmLE_REFL
    , thmNOT_EVEN
    , thmNOT_ODD
    , thmADD_CLAUSES
    , thmLE_SUC
    , thmLT_SUC
    , wopNUM
    , thmSUB_SUC
    , thmEVEN_OR_ODD
    , thmEVEN_AND_ODD
    , thmLET_CASES
    , thmEQ_IMP_LE
    , thmADD_SYM
    , thmEQ_ADD_LCANCEL
    , thmBIT0
    , thmMULT_0
    , thmADD_ASSOC
    , thmADD_EQ_0
    , thmLT_0
    , thmLT_ADD
    , thmADD_SUB
    , thmLT_REFL
    , thmSUB_EQ_0
    , thmLE_CASES
    , thmLE_ANTISYM
    , thmLET_ANTISYM
    , thmEVEN_ADD
    , thmLE_TRANS
    , thmSUB_REFL
    , thmLE_ADD
    , thmLTE_CASES
    , thmSUB_ADD_LCANCEL
    , thmBIT0_THM
    , thmBIT1
    , thmMULT_SUC
    , thmNOT_LE
    , thmNOT_LT
    , thmLE_EXISTS
    , thmLT_EXISTS
    , thmLT_ADDR
    , thmADD_SUB2
    , thmLTE_ANTISYM
    , thmLE_LT
    , thmARITH_ZERO
    , thmADD_AC
    , thmODD_ADD
    , thmEQ_ADD_RCANCEL
    , thmLTE_TRANS
    , thmADD_SUBR2
    , thmEQ_ADD_LCANCEL_0
    , thmLE_ADDR
    , thmBIT1_THM
    , thmLT_ADD_LCANCEL
    , thmLE_ADD_LCANCEL
    , thmARITH_SUC
    , thmARITH_PRE
    , thmARITH_ADD
    , thmARITH_EVEN
    , thmARITH_ODD
    , thmLE_ADD2
    , thmADD_SUBR
    , thmLT_LE
    , thmLET_ADD2
    , thmADD1
    , thmMULT_CLAUSES
    , thmLT_IMP_LE
    , thmLE_ADD_RCANCEL
    , thmLTE_ADD2
    , thmMULT_SYM
    , thmLEFT_ADD_DISTRIB
    , thmLE_MULT_LCANCEL
    , thmLT_MULT_LCANCEL
    , thmMULT_EQ_0
    , thmEQ_MULT_LCANCEL
    , thmEVEN_MULT
    , thmEXP_EQ_0
    , thmLT_ADD2
    , thmRIGHT_ADD_DISTRIB
    , thmLEFT_SUB_DISTRIB
    , thmEVEN_DOUBLE
    , thmLE_MULT_RCANCEL
    , thmDIVMOD_EXIST
    , thmMULT_2
    , thmDIVMOD_EXIST_0
    , specDIVISION_0
    , defMinimal
    , thmARITH_MULT
    , thmMULT_ASSOC
    , thmLE_MULT2
    , thmRIGHT_SUB_DISTRIB
    , thmARITH_LE
    , thmEXP_ADD
    , thmMULT_AC
    , thmARITH_LT
    , thmARITH_GE
    , thmARITH_EQ
    , thmONE
    , thmTWO
    , thmARITH_EXP 
    , thmARITH_GT
    , thmARITH_SUB
    , thmARITH_0
    , thmBITS_INJ
    , thmSUB_ELIM
    , thmEXP_2
    , convNUM_CANCEL
    , ruleLE_IMP
    , thmDIVISION
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition, getSpecification)

import HaskHOL.Lib.Pair
import HaskHOL.Lib.Nums
import HaskHOL.Lib.Recursion

import qualified HaskHOL.Lib.Arith.Base as Base
import HaskHOL.Lib.Arith.Context
import HaskHOL.Lib.Arith.PQ


defPRE :: ArithCtxt thry => HOL cls thry HOLThm
defPRE = cacheProof "defPRE" ctxtArith $ getRecursiveDefinition "PRE"

defADD :: ArithCtxt thry => HOL cls thry HOLThm
defADD = cacheProof "defADD" ctxtArith $ getRecursiveDefinition "+"

defMULT :: ArithCtxt thry => HOL cls thry HOLThm
defMULT = cacheProof "defMULT" ctxtArith $ getRecursiveDefinition "*"

defEXP :: ArithCtxt thry => HOL cls thry HOLThm
defEXP = cacheProof "defEXP" ctxtArith $ getRecursiveDefinition "EXP"

defLE :: ArithCtxt thry => HOL cls thry HOLThm
defLE = cacheProof "defLE" ctxtArith $ getRecursiveDefinition "<="

defLT :: ArithCtxt thry => HOL cls thry HOLThm
defLT = cacheProof "defLT" ctxtArith $ getRecursiveDefinition "<"

defGE :: ArithCtxt thry => HOL cls thry HOLThm
defGE = cacheProof "defGE" ctxtArith $ getDefinition ">="

defGT :: ArithCtxt thry => HOL cls thry HOLThm
defGT = cacheProof "defGT" ctxtArith $ getDefinition ">"

defMAX :: ArithCtxt thry => HOL cls thry HOLThm
defMAX = cacheProof "defMAX" ctxtArith $ getDefinition "MAX"

defMIN :: ArithCtxt thry => HOL cls thry HOLThm
defMIN = cacheProof "defMIN" ctxtArith $ getDefinition "MIN"

defEVEN :: ArithCtxt thry => HOL cls thry HOLThm
defEVEN = cacheProof "defEVEN" ctxtArith $ getRecursiveDefinition "EVEN"

defODD :: ArithCtxt thry => HOL cls thry HOLThm
defODD = cacheProof "defODD" ctxtArith $ getRecursiveDefinition "ODD"

defSUB :: ArithCtxt thry => HOL cls thry HOLThm
defSUB = cacheProof "defSUB" ctxtArith $ getRecursiveDefinition "-"

defFACT :: ArithCtxt thry => HOL cls thry HOLThm
defFACT = cacheProof "defFACT" ctxtArith $ getRecursiveDefinition "FACT"
       
specDIVISION_0 :: ArithCtxt thry => HOL cls thry HOLThm
specDIVISION_0 = cacheProof "specDIVISION_0" ctxtArith $ 
    getSpecification ["DIV", "MOD"]

defMinimal :: ArithCtxt thry => HOL cls thry HOLThm
defMinimal = cacheProof "defMinimal" ctxtArith $ getDefinition "minimal"


-- theorems
thmADD_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_0 = cacheProof "thmADD_0" ctxtArith Base.thmADD_0

thmADD_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUC = cacheProof "thmADD_SUC" ctxtArith Base.thmADD_SUC

thmLE_SUC_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_SUC_LT = cacheProof "thmLE_SUC_LT" ctxtArith Base.thmLE_SUC_LT

thmLT_SUC_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_SUC_LE = cacheProof "thmLT_SUC_LE" ctxtArith Base.thmLT_SUC_LE

thmLE_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_0 = cacheProof "thmLE_0" ctxtArith Base.thmLE_0

wfNUM_PRIM :: ArithCtxt thry => HOL cls thry HOLThm
wfNUM_PRIM = cacheProof "wfNUM_PRIM" ctxtArith Base.wfNUM_PRIM

thmSUB_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_0 = cacheProof "thmSUB_0" ctxtArith Base.thmSUB_0

thmSUB_PRESUC :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_PRESUC = cacheProof "thmSUB_PRESUC" ctxtArith Base.thmSUB_PRESUC

thmLE_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_REFL = cacheProof "thmLE_REFL" ctxtArith Base.thmLE_REFL

thmNOT_EVEN :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_EVEN = cacheProof "thmNOT_EVEN" ctxtArith Base.thmNOT_EVEN

thmNOT_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_ODD = cacheProof "thmNOT_ODD" ctxtArith Base.thmNOT_ODD

thmADD_CLAUSES :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_CLAUSES = cacheProof "thmADD_CLAUSES" ctxtArith Base.thmADD_CLAUSES

thmLE_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_SUC = cacheProof "thmLE_SUC" ctxtArith Base.thmLE_SUC

thmLT_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_SUC = cacheProof "thmLT_SUC" ctxtArith Base.thmLT_SUC

wopNUM :: ArithCtxt thry => HOL cls thry HOLThm
wopNUM = cacheProof "wopNUM" ctxtArith Base.wopNUM

thmSUB_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_SUC = cacheProof "thmSUB_SUC" ctxtArith Base.thmSUB_SUC

thmEVEN_OR_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_OR_ODD = cacheProof "thmEVEN_OR_ODD" ctxtArith Base.thmEVEN_OR_ODD

thmEVEN_AND_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_AND_ODD = cacheProof "thmEVEN_AND_ODD" ctxtArith Base.thmEVEN_AND_ODD

thmLET_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_CASES = cacheProof "thmLET_CASES" ctxtArith Base.thmLET_CASES

thmEQ_IMP_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_IMP_LE = cacheProof "thmEQ_IMP_LE" ctxtArith Base.thmEQ_IMP_LE

thmADD_SYM :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SYM = cacheProof "thmADD_SYM" ctxtArith Base.thmADD_SYM

thmEQ_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL = 
    cacheProof "thmEQ_ADD_LCANCEL" ctxtArith Base.thmEQ_ADD_LCANCEL

thmBIT0 :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT0 = cacheProof "thmBIT0" ctxtArith Base.thmBIT0

thmMULT_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_0 = cacheProof "thmMULT_0" ctxtArith Base.thmMULT_0

thmADD_ASSOC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_ASSOC = cacheProof "thmADD_ASSOC" ctxtArith Base.thmADD_ASSOC

thmADD_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_EQ_0 = cacheProof "thmADD_EQ_0" ctxtArith Base.thmADD_EQ_0

thmLT_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_0 = cacheProof "thmLT_0" ctxtArith Base.thmLT_0

thmLT_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD = cacheProof "thmLT_ADD" ctxtArith Base.thmLT_ADD

thmADD_SUB :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUB = cacheProof "thmADD_SUB" ctxtArith Base.thmADD_SUB

thmLT_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_REFL = cacheProof "thmLT_REFL" ctxtArith Base.thmLT_REFL

thmSUB_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_EQ_0 = cacheProof "thmSUB_EQ_0" ctxtArith Base.thmSUB_EQ_0

thmLE_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_CASES = cacheProof "thmLE_CASES" ctxtArith Base.thmLE_CASES

thmLE_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ANTISYM = cacheProof "thmLE_ANTISYM" ctxtArith Base.thmLE_ANTISYM

thmLET_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_ANTISYM = cacheProof "thmLET_ANTISYM" ctxtArith Base.thmLET_ANTISYM

thmEVEN_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_ADD = cacheProof "thmEVEN_ADD" ctxtArith Base.thmEVEN_ADD

thmLE_TRANS :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_TRANS = cacheProof "thmLE_TRANS" ctxtArith Base.thmLE_TRANS

thmSUB_REFL :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_REFL = cacheProof "thmSUB_REFL" ctxtArith Base.thmSUB_REFL

thmLE_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD = cacheProof "thmLE_ADD" ctxtArith Base.thmLE_ADD

thmLTE_CASES :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_CASES = cacheProof "thmLTE_CASES" ctxtArith Base.thmLTE_CASES

thmSUB_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_ADD_LCANCEL = 
    cacheProof "thmSUB_ADD_LCANCEL" ctxtArith Base.thmSUB_ADD_LCANCEL

thmBIT0_THM :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT0_THM = cacheProof "thmBIT0_THM" ctxtArith Base.thmBIT0_THM

thmBIT1 :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT1 = cacheProof "thmBIT1" ctxtArith Base.thmBIT1

thmMULT_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_SUC = cacheProof "thmMULT_SUC" ctxtArith Base.thmMULT_SUC

thmNOT_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_LE = cacheProof "thmNOT_LE" ctxtArith Base.thmNOT_LE

thmNOT_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmNOT_LT = cacheProof "thmNOT_LT" ctxtArith Base.thmNOT_LT

thmLE_EXISTS :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_EXISTS = cacheProof "thmLE_EXISTS" ctxtArith Base.thmLE_EXISTS

thmLT_EXISTS :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_EXISTS = cacheProof "thmLT_EXISTS" ctxtArith Base.thmLT_EXISTS

thmLT_ADDR :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADDR = cacheProof "thmLT_ADDR" ctxtArith Base.thmLT_ADDR

thmADD_SUB2 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUB2 = cacheProof "thmADD_SUB2" ctxtArith Base.thmADD_SUB2

thmLTE_ANTISYM :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_ANTISYM = cacheProof "thmLTE_ANTISYM" ctxtArith Base.thmLTE_ANTISYM

thmLE_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_LT = cacheProof "thmLE_LT" ctxtArith Base.thmLE_LT

thmARITH_ZERO :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ZERO = cacheProof "thmARITH_ZERO" ctxtArith Base.thmARITH_ZERO

thmADD_AC :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_AC = cacheProof "thmADD_AC" ctxtArith Base.thmADD_AC

thmODD_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmODD_ADD = cacheProof "thmODD_ADD" ctxtArith Base.thmODD_ADD

thmEQ_ADD_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_RCANCEL = 
    cacheProof "thmEQ_ADD_RCANCEL" ctxtArith Base.thmEQ_ADD_RCANCEL

thmLTE_TRANS :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_TRANS = cacheProof "thmLTE_TRANS" ctxtArith Base.thmLTE_TRANS

thmADD_SUBR2 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUBR2 = cacheProof "thmADD_SUBR2" ctxtArith Base.thmADD_SUBR2

thmEQ_ADD_LCANCEL_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_ADD_LCANCEL_0 = 
    cacheProof "thmEQ_ADD_LCANCEL_0" ctxtArith Base.thmEQ_ADD_LCANCEL_0

thmLE_ADDR :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADDR = cacheProof "thmLE_ADDR" ctxtArith Base.thmLE_ADDR

thmBIT1_THM :: ArithCtxt thry => HOL cls thry HOLThm
thmBIT1_THM = cacheProof "thmBIT1_THM" ctxtArith Base.thmBIT1_THM

thmLT_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD_LCANCEL = 
    cacheProof "thmLT_ADD_LCANCEL" ctxtArith Base.thmLT_ADD_LCANCEL

thmLE_ADD_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD_LCANCEL = 
    cacheProof "thmLE_ADD_LCANCEL" ctxtArith Base.thmLE_ADD_LCANCEL

thmARITH_SUC :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_SUC = cacheProof "thmARITH_SUC" ctxtArith Base.thmARITH_SUC

thmARITH_PRE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_PRE = cacheProof "thmARITH_PRE" ctxtArith Base.thmARITH_PRE

thmARITH_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ADD = cacheProof "thmARITH_ADD" ctxtArith Base.thmARITH_ADD

thmARITH_EVEN :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EVEN = cacheProof "thmARITH_EVEN" ctxtArith Base.thmARITH_EVEN

thmARITH_ODD :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_ODD = cacheProof "thmARITH_ODD" ctxtArith Base.thmARITH_ODD

thmLE_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD2 = cacheProof "thmLE_ADD2" ctxtArith Base.thmLE_ADD2

thmADD_SUBR :: ArithCtxt thry => HOL cls thry HOLThm
thmADD_SUBR = cacheProof "thmADD_SUBR" ctxtArith Base.thmADD_SUBR

thmLT_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_LE = cacheProof "thmLT_LE" ctxtArith Base.thmLT_LE

thmLET_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLET_ADD2 = cacheProof "thmLET_ADD2" ctxtArith Base.thmLET_ADD2

thmADD1 :: ArithCtxt thry => HOL cls thry HOLThm
thmADD1 = cacheProof "thmADD1" ctxtArith Base.thmADD1

thmMULT_CLAUSES :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_CLAUSES = cacheProof "thmMULT_CLAUSES" ctxtArith Base.thmMULT_CLAUSES

thmLT_IMP_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_IMP_LE = cacheProof "thmLT_IMP_LE" ctxtArith Base.thmLT_IMP_LE

thmLE_ADD_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_ADD_RCANCEL = 
    cacheProof "thmLE_ADD_RCANCEL" ctxtArith Base.thmLE_ADD_RCANCEL

thmLTE_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLTE_ADD2 = cacheProof "thmLTE_ADD2" ctxtArith Base.thmLTE_ADD2

thmMULT_SYM :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_SYM = cacheProof "thmMULT_SYM" ctxtArith Base.thmMULT_SYM

thmLEFT_ADD_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmLEFT_ADD_DISTRIB = 
    cacheProof "thmLEFT_ADD_DISTRIB" ctxtArith Base.thmLEFT_ADD_DISTRIB

thmLE_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT_LCANCEL = 
    cacheProof "thmLE_MULT_LCANCEL" ctxtArith Base.thmLE_MULT_LCANCEL

thmLT_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_MULT_LCANCEL = 
    cacheProof "thmLT_MULT_LCANCEL" ctxtArith Base.thmLT_MULT_LCANCEL

thmMULT_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_EQ_0 = cacheProof "thmMULT_EQ_0" ctxtArith Base.thmMULT_EQ_0

thmEQ_MULT_LCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmEQ_MULT_LCANCEL = 
    cacheProof "thmEQ_MULT_LCANCEL" ctxtArith Base.thmEQ_MULT_LCANCEL

thmEVEN_MULT :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_MULT = cacheProof "thmEVEN_MULT" ctxtArith Base.thmEVEN_MULT

thmEXP_EQ_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_EQ_0 = cacheProof "thmEXP_EQ_0" ctxtArith Base.thmEXP_EQ_0

thmLT_ADD2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLT_ADD2 = cacheProof "thmLT_ADD2" ctxtArith Base.thmLT_ADD2

thmRIGHT_ADD_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmRIGHT_ADD_DISTRIB = 
    cacheProof "thmRIGHT_ADD_DISTRIB" ctxtArith Base.thmRIGHT_ADD_DISTRIB

thmLEFT_SUB_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmLEFT_SUB_DISTRIB = 
    cacheProof "thmLEFT_SUB_DISTRIB" ctxtArith Base.thmLEFT_SUB_DISTRIB

thmEVEN_DOUBLE :: ArithCtxt thry => HOL cls thry HOLThm
thmEVEN_DOUBLE = cacheProof "thmEVEN_DOUBLE" ctxtArith Base.thmEVEN_DOUBLE

thmLE_MULT_RCANCEL :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT_RCANCEL = 
    cacheProof "thmLE_MULT_RCANCEL" ctxtArith Base.thmLE_MULT_RCANCEL

thmDIVMOD_EXIST :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST = cacheProof "thmDIVMOD_EXIST" ctxtArith Base.thmDIVMOD_EXIST

thmMULT_2 :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_2 = cacheProof "thmMULT_2" ctxtArith Base.thmMULT_2

thmARITH_MULT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_MULT = cacheProof "thmARITH_MULT" ctxtArith Base.thmARITH_MULT

thmMULT_ASSOC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_ASSOC = cacheProof "thmMULT_ASSOC" ctxtArith Base.thmMULT_ASSOC

thmLE_MULT2 :: ArithCtxt thry => HOL cls thry HOLThm
thmLE_MULT2 = cacheProof "thmLE_MULT2" ctxtArith Base.thmLE_MULT2

thmRIGHT_SUB_DISTRIB :: ArithCtxt thry => HOL cls thry HOLThm
thmRIGHT_SUB_DISTRIB = 
    cacheProof "thmRIGHT_SUB_DISTRIB" ctxtArith Base.thmRIGHT_SUB_DISTRIB

thmARITH_LE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_LE = cacheProof "thmARITH_LE" ctxtArith Base.thmARITH_LE

thmMULT_AC :: ArithCtxt thry => HOL cls thry HOLThm
thmMULT_AC = cacheProof "thmMULT_AC" ctxtArith Base.thmMULT_AC

thmARITH_LT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_LT = cacheProof "thmARITH_LT" ctxtArith Base.thmARITH_LT

thmARITH_GE :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_GE = cacheProof "thmARITH_GE" ctxtArith Base.thmARITH_GE

thmARITH_EQ :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EQ = cacheProof "thmARITH_EQ" ctxtArith Base.thmARITH_EQ

thmEXP_ADD :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_ADD = cacheProof "thmEXP_ADD" ctxtArith Base.thmARITH_EQ

thmDIVMOD_EXIST_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVMOD_EXIST_0 = 
    cacheProof "thmDIVMOD_EXIST_0" ctxtArith Base.thmDIVMOD_EXIST_0

thmONE :: ArithCtxt thry => HOL cls thry HOLThm
thmONE = cacheProof "thmONE" ctxtArith $
    prove "1 = SUC 0" $ 
      tacREWRITE [thmBIT1, ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL]

thmTWO :: ArithCtxt thry => HOL cls thry HOLThm
thmTWO = cacheProof "thmTWO" ctxtArith $
    prove "2 = SUC 1" $ 
      tacREWRITE [ thmBIT0, thmBIT1
                 , ruleREWRITE [defNUMERAL] thmADD_CLAUSES, defNUMERAL ]

thmARITH_GT :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_GT = cacheProof "thmARITH_GT" ctxtArith $
    ruleREWRITE [ruleGSYM defGE, ruleGSYM defGT] thmARITH_LT

thmARITH_SUB :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_SUB = cacheProof "thmARITH_SUB" ctxtArith .
    prove [str| (!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\
                (_0 - _0 = _0) /\
                (!n. _0 - BIT0 n = _0) /\
                (!n. _0 - BIT1 n = _0) /\
                (!n. BIT0 n - _0 = BIT0 n) /\
                (!n. BIT1 n - _0 = BIT1 n) /\
                (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\
                (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\
                (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\
                (!m n. BIT1 m - BIT1 n = BIT0 (m - n)) |] $
      tacREWRITE [defNUMERAL, ruleDENUMERAL thmSUB_0] `_THEN`
      tacPURE_REWRITE [thmBIT0, thmBIT1] `_THEN`
      tacREWRITE [ ruleGSYM thmMULT_2, thmSUB_SUC, thmLEFT_SUB_DISTRIB ] `_THEN`
      tacREWRITE [defSUB] `_THEN` _REPEAT tacGEN `_THEN` tacCOND_CASES `_THEN`
      tacREWRITE [ruleDENUMERAL thmSUB_EQ_0] `_THEN`
      tacRULE_ASSUM (ruleREWRITE [thmNOT_LE]) `_THEN`
      tacASM_REWRITE [thmLE_SUC_LT, thmLT_MULT_LCANCEL, thmARITH_EQ] `_THEN`
      _POP_ASSUM (_CHOOSE_THEN tacSUBST1 . ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacREWRITE [thmADD1, thmLEFT_ADD_DISTRIB] `_THEN`
      tacREWRITE [thmADD_SUB2, ruleGSYM thmADD_ASSOC]

thmARITH_EXP :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_EXP = cacheProof "thmARITH_EXP" ctxtArith $
    prove [str| (!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\
                (_0 EXP _0 = BIT1 _0) /\
                (!m. (BIT0 m) EXP _0 = BIT1 _0) /\
                (!m. (BIT1 m) EXP _0 = BIT1 _0) /\
                (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\
                (!m n. (BIT0 m) EXP (BIT0 n) = 
                       ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
                (!m n. (BIT1 m) EXP (BIT0 n) = 
                       ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\
                (!n. _0 EXP (BIT1 n) = _0) /\
                (!m n. (BIT0 m) EXP (BIT1 n) =
                       BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\
                (!m n. (BIT1 m) EXP (BIT1 n) =
                       BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) |] $
      tacREWRITE [defNUMERAL] `_THEN` _REPEAT tacSTRIP `_THEN`
      _TRY (tacGEN_REWRITE (convLAND . convRAND) [thmBIT0, thmBIT1]) `_THEN`
      tacREWRITE [ ruleDENUMERAL defEXP, ruleDENUMERAL thmMULT_CLAUSES
                 , thmEXP_ADD ]

thmARITH_0 :: ArithCtxt thry => HOL cls thry HOLThm
thmARITH_0 = cacheProof "thmARITH_0" ctxtArith $
    ruleMESON [defNUMERAL, thmADD_CLAUSES] [str| m + _0 = m /\ _0 + n = n |]

thmBITS_INJ :: ArithCtxt thry => HOL cls thry HOLThm
thmBITS_INJ = cacheProof "thmBITS_INJ" ctxtArith .
    prove [str| (BIT0 m = BIT0 n <=> m = n) /\
                (BIT1 m = BIT1 n <=> m = n) |] $
      tacREWRITE [thmBIT0, thmBIT1] `_THEN`
      tacREWRITE [ruleGSYM thmMULT_2] `_THEN`
      tacREWRITE [thmSUC_INJ, thmEQ_MULT_LCANCEL, thmARITH_EQ]

thmSUB_ELIM :: ArithCtxt thry => HOL cls thry HOLThm
thmSUB_ELIM = cacheProof "thmSUB_ELIM" ctxtArith $
    prove [str| P(a - b) <=> !d. a = b + d \/ a < b /\ d = 0 ==> P d |] $
      tacDISJ_CASES (ruleSPECL ["a:num", "b:num"] =<< thmLTE_CASES) `_THENL`
      [ tacASM_MESON [thmNOT_LT, thmSUB_EQ_0, thmLT_IMP_LE, thmLE_ADD]
      , _ALL
      ] `_THEN`
      _FIRST_ASSUM (_X_CHOOSE_THEN "e:num" tacSUBST1 . 
                     ruleREWRITE [thmLE_EXISTS]) `_THEN`
      tacSIMP [ thmADD_SUB2, ruleGSYM thmNOT_LE
              , thmLE_ADD, thmEQ_ADD_LCANCEL ] `_THEN` 
      tacMESON_NIL

thmEXP_2 :: ArithCtxt thry => HOL cls thry HOLThm
thmEXP_2 = cacheProof "thmEXP_2" ctxtArith .
    prove "!n. n EXP 2 = n * n" $
      tacREWRITE [ thmBIT0_THM, thmBIT1_THM, defEXP
                 , thmEXP_ADD, thmMULT_CLAUSES, thmADD_CLAUSES ]

convNUM_CANCEL :: ArithCtxt thry => Conversion cls thry
convNUM_CANCEL = Conv $ \ tm ->
    do tmAdd <- serve [arith| (+) |]
       tmeq <- serve [arith| (=) :num->num->bool |]
       let (l, r) = fromJust $ destEq tm
           lats = sort (<=) $ binops tmAdd l
           rats = sort (<=) $ binops tmAdd r
           (i, lats', rats') = minter [] [] [] lats rats
       let l' = fromRight $ listMkBinop tmAdd (i ++ lats')
           r' = fromRight $ listMkBinop tmAdd (i ++ rats')
       lth <- ruleAC =<< mkEq l l'
       rth <- ruleAC =<< mkEq r r'
       let eth = fromRight $ liftM1 primMK_COMB (ruleAP_TERM tmeq lth) rth
       ruleGEN_REWRITE (convRAND . _REPEAT) 
         [thmEQ_ADD_LCANCEL, thmEQ_ADD_LCANCEL_0, convNUM_CANCEL_pth] eth
  where minter :: [HOLTerm] -> [HOLTerm] -> [HOLTerm] -> [HOLTerm] -> [HOLTerm] 
               -> ([HOLTerm], [HOLTerm], [HOLTerm])
        minter i l1' l2' [] l2 = (i, l1', l2' ++ l2)
        minter i l1' l2' l1 [] = (i, l1 ++ l1', l2')
        minter i l1' l2' l1@(h1:t1) l2@(h2:t2)
            | h1 == h2 = minter (h1:i) l1' l2' t1 t2
            | h1 < h2 = minter i (h1:l1') l2' t1 l2
            | otherwise = minter i l1' (h2:l2') l1 t2

        ruleAC :: ArithCtxt thry => HOLTerm 
               -> HOL cls thry HOLThm
        ruleAC = runConv (convAC thmADD_AC)
            
        convNUM_CANCEL_pth :: ArithCtxt thry 
                           => HOL cls thry HOLThm
        convNUM_CANCEL_pth = cacheProof "convNUM_CANCEL_pth" ctxtArith $
            ruleGEN_REWRITE (funpow 2 convBINDER . convLAND) 
              [thmEQ_SYM_EQ] =<< thmEQ_ADD_LCANCEL_0

ruleLE_IMP :: (ArithCtxt thry, HOLThmRep thm cls thry) => thm 
           -> HOL cls thry HOLThm
ruleLE_IMP th =
    ruleGEN_ALL =<< ruleMATCH_MP ruleLE_IMP_pth =<< ruleSPEC_ALL th
  where ruleLE_IMP_pth :: ArithCtxt thry 
                       => HOL cls thry HOLThm
        ruleLE_IMP_pth = cacheProof "ruleLE_IMP_pth" ctxtArith $
            rulePURE_ONCE_REWRITE[thmIMP_CONJ] =<< thmLE_TRANS

thmDIVISION :: ArithCtxt thry => HOL cls thry HOLThm
thmDIVISION = cacheProof "thmDIVISION" ctxtArith .
    prove [str| !m n. ~(n = 0) ==> 
                      (m = m DIV n * n + m MOD n) /\ m MOD n < n |] $
      tacMESON [specDIVISION_0]
