module HaskHOL.Lib.IndTypes.Base where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getSpecification, getDefinition, newDefinition)

import HaskHOL.Lib.WF

import HaskHOL.Lib.IndTypes.Pre2

--EvNote: need list for distintness and injectivity stores because of dupe keys
data RectypeNet = RectypeNet !(Net GConversion) deriving Typeable

deriveSafeCopy 0 'base ''RectypeNet

getNet :: Query RectypeNet (Net GConversion)
getNet =
    do (RectypeNet net) <- ask
       return net

putNet :: Net GConversion -> Update RectypeNet ()
putNet net = put (RectypeNet net)

makeAcidic ''RectypeNet ['getNet, 'putNet]

data InductiveTypes = 
    InductiveTypes !(Map Text (HOLThm, HOLThm)) deriving Typeable

putInductiveTypes :: Map Text (HOLThm, HOLThm) -> Update InductiveTypes ()
putInductiveTypes m =
    put (InductiveTypes m)

getInductiveTypes :: Query InductiveTypes (Map Text (HOLThm, HOLThm))
getInductiveTypes =
    do (InductiveTypes m) <- ask
       return m

addInductiveType :: Text -> (HOLThm, HOLThm) -> Update InductiveTypes ()
addInductiveType s ths =
    do (InductiveTypes m) <- get
       put (InductiveTypes (mapInsert s ths m))

getInductiveType :: Text -> Query InductiveTypes (Maybe (HOLThm, HOLThm))
getInductiveType s =
    do (InductiveTypes m) <- ask
       return $! mapAssoc s m

deriveSafeCopy 0 'base ''InductiveTypes

makeAcidic ''InductiveTypes 
  ['putInductiveTypes, 'getInductiveTypes, 'addInductiveType, 'getInductiveType]

data DistinctnessStore = 
    DistinctnessStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''DistinctnessStore

getDistinctnessStore :: Query DistinctnessStore [(Text, HOLThm)]
getDistinctnessStore = 
    do (DistinctnessStore m) <- ask
       return m

addDistinctnessStore :: Text -> [HOLThm] -> Update DistinctnessStore ()
addDistinctnessStore tyname ths =
    do (DistinctnessStore m) <- get
       put (DistinctnessStore (map (\ x -> (tyname, x)) ths ++ m))

putDistinctnessStore :: [(Text, HOLThm)] -> Update DistinctnessStore ()
putDistinctnessStore m =
    put (DistinctnessStore m)

makeAcidic ''DistinctnessStore 
    ['getDistinctnessStore, 'addDistinctnessStore, 'putDistinctnessStore]

data InjectivityStore = InjectivityStore ![(Text, HOLThm)] deriving Typeable

deriveSafeCopy 0 'base ''InjectivityStore

getInjectivityStore :: Query InjectivityStore [(Text, HOLThm)]
getInjectivityStore =
    do (InjectivityStore m) <- ask
       return m

addInjectivityStore :: Text -> [HOLThm] -> Update InjectivityStore ()
addInjectivityStore tyname ths =
    do (InjectivityStore m) <- get
       put (InjectivityStore (map (\ x -> (tyname, x)) ths ++ m))

makeAcidic ''InjectivityStore ['getInjectivityStore, 'addInjectivityStore]


rehashRectypeNet :: BoolCtxt thry => HOL Theory thry ()
rehashRectypeNet =
    do acid1 <- openLocalStateHOL (DistinctnessStore [])
       ths1 <- liftM (map snd) $ queryHOL acid1 GetDistinctnessStore
       closeAcidStateHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       ths2 <- liftM (map snd) $ queryHOL acid2 GetInjectivityStore
       closeAcidStateHOL acid2
       canonThl <- foldrM (mkRewrites False) [] $ ths1 ++ ths2
       net' <- foldrM (netOfThm True) netEmpty canonThl
       acid3 <- openLocalStateHOL (RectypeNet netEmpty)
       updateHOL acid3 (PutNet net')
       closeAcidStateHOL acid3

extendRectypeNet :: WFCtxt thry => (Text, (Int, HOLThm, HOLThm)) 
                 -> HOL Theory thry ()
extendRectypeNet (tyname, (_, _, rth)) =
    do ths1 <- liftM (:[]) (proveConstructorsDistinct rth) <|> return []
       ths2 <- liftM (:[]) (proveConstructorsInjective rth) <|> return []
       acid1 <- openLocalStateHOL (DistinctnessStore [])
       updateHOL acid1 (AddDistinctnessStore tyname ths1)
       closeAcidStateHOL acid1
       acid2 <- openLocalStateHOL (InjectivityStore [])
       updateHOL acid2 (AddInjectivityStore tyname ths2)
       closeAcidStateHOL acid2
       rehashRectypeNet

basicRectypeNet :: BoolCtxt thry => HOL cls thry (Net GConversion)
basicRectypeNet =
    do acid <- openLocalStateHOL (RectypeNet netEmpty)
       net <- queryHOL acid GetNet
       closeAcidStateHOL acid
       return net
