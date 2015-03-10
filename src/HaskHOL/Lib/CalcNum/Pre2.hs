{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, TemplateHaskell,
             TypeFamilies #-}
module HaskHOL.Lib.CalcNum.Pre2 where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Arith
import HaskHOL.Lib.WF.Context

import HaskHOL.Lib.CalcNum.Pre

import Data.Vector (Vector)
import qualified Data.Vector as V

thmARITH :: WFCtxt thry => HOL cls thry HOLThm
thmARITH = cacheProof "thmARITH" ctxtWF $ foldr1M ruleCONJ =<< 
    sequence [ thmARITH_ZERO, thmARITH_SUC, thmARITH_PRE
             , thmARITH_ADD, thmARITH_MULT, thmARITH_EXP
             , thmARITH_EVEN, thmARITH_ODD, thmARITH_EQ
             , thmARITH_LE, thmARITH_LT, thmARITH_GE
             , thmARITH_GT, thmARITH_SUB
             ]

-- Lookup arrays for numeral conversions
data ADDClauses = ADDClauses !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''ADDClauses

getAddClauses :: Query ADDClauses (Vector HOLThm)
getAddClauses =
    do (ADDClauses v) <- ask
       return v

putAddClauses :: Vector HOLThm -> Update ADDClauses ()
putAddClauses v =
    put (ADDClauses v)

makeAcidic ''ADDClauses ['getAddClauses, 'putAddClauses]

data ADDFlags = ADDFlags !(Vector Int) deriving Typeable

deriveSafeCopy 0 'base ''ADDFlags

getAddFlags :: Query ADDFlags (Vector Int)
getAddFlags =
    do (ADDFlags v) <- ask
       return v

putAddFlags :: Vector Int -> Update ADDFlags ()
putAddFlags v =
    put (ADDFlags v)

makeAcidic ''ADDFlags ['getAddFlags, 'putAddFlags]


data ADCClauses = ADCClauses !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''ADCClauses

getAdcClauses :: Query ADCClauses (Vector HOLThm)
getAdcClauses =
    do (ADCClauses v) <- ask
       return v

putAdcClauses :: Vector HOLThm -> Update ADCClauses ()
putAdcClauses v =
    put (ADCClauses v)

makeAcidic ''ADCClauses ['getAdcClauses, 'putAdcClauses]

data ADCFlags = ADCFlags !(Vector Int) deriving Typeable

deriveSafeCopy 0 'base ''ADCFlags

getAdcFlags :: Query ADCFlags (Vector Int)
getAdcFlags =
    do (ADCFlags v) <- ask
       return v

putAdcFlags :: Vector Int -> Update ADCFlags ()
putAdcFlags v =
    put (ADCFlags v)

makeAcidic ''ADCFlags ['getAdcFlags, 'putAdcFlags]


addClauses :: WFCtxt thry => HOL cls thry (Vector HOLThm)
addClauses =
    do acid <- openLocalStateHOLBase (ADDClauses V.empty)
       v <- queryHOL acid GetAddClauses
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
           else do (clauses, flags) <- liftM unzip $ 
                                         mapM (mkClauses False) =<< starts
                   let v' = V.fromList clauses
                   acid' <- openLocalStateHOLBase (ADDClauses V.empty)
                   updateHOLUnsafe acid' (PutAddClauses v')
                   createCheckpointAndCloseHOL acid'
                   acid2 <- openLocalStateHOLBase (ADDFlags V.empty)
                   updateHOLUnsafe acid2 (PutAddFlags (V.fromList flags))
                   createCheckpointAndCloseHOL acid2
                   return v'

addFlags :: WFCtxt thry => HOL cls thry (Vector Int)
addFlags =
    do acid <- openLocalStateHOLBase (ADDFlags V.empty)
       v <- queryHOL acid GetAddFlags
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
           else do (clauses, flags) <- liftM unzip $ 
                                         mapM (mkClauses False) =<< starts
                   let v' = V.fromList flags
                   acid' <- openLocalStateHOLBase (ADDClauses V.empty)
                   updateHOLUnsafe acid' (PutAddClauses (V.fromList clauses))
                   createCheckpointAndCloseHOL acid'
                   acid2 <- openLocalStateHOLBase (ADDFlags V.empty)
                   updateHOLUnsafe acid2 (PutAddFlags v')
                   createCheckpointAndCloseHOL acid2
                   return v'


adcClauses :: WFCtxt thry => HOL cls thry (Vector HOLThm)
adcClauses =
    do acid <- openLocalStateHOLBase (ADCClauses V.empty)
       v <- queryHOL acid GetAdcClauses
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
           else do (clauses, flags) <- liftM unzip $ 
                                         mapM (mkClauses True) =<< starts
                   let v' = V.fromList clauses
                   acid' <- openLocalStateHOLBase (ADCClauses V.empty)
                   updateHOLUnsafe acid' (PutAdcClauses v')
                   createCheckpointAndCloseHOL acid'
                   acid2 <- openLocalStateHOLBase (ADCFlags V.empty)
                   updateHOLUnsafe acid2 (PutAdcFlags (V.fromList flags))
                   createCheckpointAndCloseHOL acid2
                   return v'

adcFlags :: WFCtxt thry => HOL cls thry (Vector Int)
adcFlags =
    do acid <- openLocalStateHOLBase (ADCFlags V.empty)
       v <- queryHOL acid GetAdcFlags
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
           else do (clauses, flags) <- liftM unzip $ 
                                         mapM (mkClauses True) =<< starts
                   let v' = V.fromList flags
                   acid' <- openLocalStateHOLBase (ADCClauses V.empty)
                   updateHOLUnsafe acid' (PutAdcClauses (V.fromList clauses))
                   createCheckpointAndCloseHOL acid'
                   acid2 <- openLocalStateHOLBase (ADCFlags V.empty)
                   updateHOLUnsafe acid2 (PutAdcFlags v')
                   createCheckpointAndCloseHOL acid2
                   return v'

data SHIFTPths1 = SHIFTPths1 !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''SHIFTPths1

getShiftPths1 :: Query SHIFTPths1 (Vector HOLThm)
getShiftPths1 =
    do (SHIFTPths1 v) <- ask
       return v

putShiftPths1 :: Vector HOLThm -> Update SHIFTPths1 ()
putShiftPths1 v =
    put (SHIFTPths1 v)

makeAcidic ''SHIFTPths1 ['getShiftPths1, 'putShiftPths1]


data SHIFTPths0 = SHIFTPths0 !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''SHIFTPths0

getShiftPths0 :: Query SHIFTPths0 (Vector HOLThm)
getShiftPths0 =
    do (SHIFTPths0 v) <- ask
       return v

putShiftPths0 :: Vector HOLThm -> Update SHIFTPths0 ()
putShiftPths0 v =
    put (SHIFTPths0 v)

makeAcidic ''SHIFTPths0 ['getShiftPths0, 'putShiftPths0]


data UNSHIFTpuths1 = UNSHIFTpuths1 !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''UNSHIFTpuths1

getUnshiftpuths1 :: Query UNSHIFTpuths1 (Vector HOLThm)
getUnshiftpuths1 =
    do (UNSHIFTpuths1 v) <- ask
       return v

putUnshiftpuths1 :: Vector HOLThm -> Update UNSHIFTpuths1 ()
putUnshiftpuths1 v =
    put (UNSHIFTpuths1 v)

makeAcidic ''UNSHIFTpuths1 ['getUnshiftpuths1, 'putUnshiftpuths1]


data UNSHIFTpuths2 = UNSHIFTpuths2 !(Vector HOLThm) deriving Typeable

deriveSafeCopy 0 'base ''UNSHIFTpuths2

getUnshiftpuths2 :: Query UNSHIFTpuths2 (Vector HOLThm)
getUnshiftpuths2 =
    do (UNSHIFTpuths2 v) <- ask
       return v

putUnshiftpuths2 :: Vector HOLThm -> Update UNSHIFTpuths2 ()
putUnshiftpuths2 v =
    put (UNSHIFTpuths2 v)

makeAcidic ''UNSHIFTpuths2 ['getUnshiftpuths2, 'putUnshiftpuths2]


convNUM_SHIFT_pths1 :: WFCtxt thry => HOL cls thry (Vector HOLThm)
convNUM_SHIFT_pths1 =
    do acid <- openLocalStateHOLBase (SHIFTPths1 V.empty)
       v <- queryHOL acid GetShiftPths1
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
          else do ths <- ruleCONJUNCTS convNUM_SHIFT_pths1'
                  let v' = V.fromList ths
                  acid' <- openLocalStateHOLBase (SHIFTPths1 V.empty)
                  updateHOLUnsafe acid (PutShiftPths1 v')
                  createCheckpointAndCloseHOL acid'
                  return v'

convNUM_SHIFT_pths0 :: WFCtxt thry => HOL cls thry (Vector HOLThm)
convNUM_SHIFT_pths0 =
    do acid <- openLocalStateHOLBase (SHIFTPths0 V.empty)
       v <- queryHOL acid GetShiftPths0
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
          else do ths <- ruleCONJUNCTS convNUM_SHIFT_pths0'
                  let v' = V.fromList ths
                  acid' <- openLocalStateHOLBase (SHIFTPths0 V.empty)
                  updateHOLUnsafe acid (PutShiftPths0 v')
                  createCheckpointAndCloseHOL acid'
                  return v'

convNUM_UNSHIFT_puths1 :: WFCtxt thry => HOL cls thry (Vector HOLThm)
convNUM_UNSHIFT_puths1 = 
    do acid <- openLocalStateHOLBase (UNSHIFTpuths1 V.empty)
       v <- queryHOL acid GetUnshiftpuths1
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
          else do ths <- ruleCONJUNCTS convNUM_UNSHIFT_puths1'
                  let v' = V.fromList ths
                  acid' <- openLocalStateHOLBase (UNSHIFTpuths1 V.empty)
                  updateHOLUnsafe acid (PutUnshiftpuths1 v')
                  createCheckpointAndCloseHOL acid'
                  return v'

convNUM_UNSHIFT_puths2 :: WFCtxt thry => HOL cls thry (Vector HOLThm)
convNUM_UNSHIFT_puths2 = 
    do acid <- openLocalStateHOLBase (UNSHIFTpuths2 V.empty)
       v <- queryHOL acid GetUnshiftpuths2
       closeAcidStateHOL acid
       if not (V.null v)
          then return v
          else do puths <- convNUM_UNSHIFT_puths1
                  ths <- mapM (\ i -> 
                               let th1 = puths V.! (i `mod` 16)
                                   th2 = puths V.! (i `div` 16) in
                                 ruleGEN_REWRITE convRAND [th1] th2) [0..256]
                  let v' = V.fromList ths
                  acid' <- openLocalStateHOLBase (UNSHIFTpuths2 V.empty)
                  updateHOLUnsafe acid (PutUnshiftpuths2 v')
                  createCheckpointAndCloseHOL acid'
                  return v'
