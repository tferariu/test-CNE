{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

--{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

-- | A general-purpose escrow contract in Plutus
module Plutus.Examples.MultiSig (
  -- $multisig
  MultiSig,
  State (..),
  Params (..),
  
  smTypedValidator,
  mkAddress,
  insert,

  -- * Exposed for test endpoints
  Input (..),
  Datum,
  Deadline,
  Label (..),
  mkValidator,
  mkPolicy,
  policy,
  versionedPolicy,
  curSymbol,
  mintingHash,
  getPid,

  -- * Coverage
  covIdx,
) where

import Control.Lens (makeClassyPrisms)
import Control.Monad (void)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)

--import PlutusTx.Prelude ()
--import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Prelude
import Prelude (Show (..), String)

import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node (
  SlotConfig,
  pSlotConfig,
  posixTimeRangeToContainedSlotRange,
 )
import Cardano.Node.Emulator.Test (testnet)
import Data.Maybe (fromJust)
import Ledger (POSIXTime, PaymentPubKeyHash (unPaymentPubKeyHash), TxId, getCardanoTxId)
import Ledger qualified
import Ledger.Address (toWitness)
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash)
import Plutus.Script.Utils.V3.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V3.Typed.Scripts qualified as V3
import Plutus.Script.Utils.V3.Scripts qualified as V3
import Plutus.Script.Utils.Value --(Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval

import PlutusLedgerApi.V1.Value qualified as V
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V3 hiding (TxId)--(Datum (Datum))
import PlutusLedgerApi.V3.Contexts hiding (TxId)--(valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId)--(OutputDatum (OutputDatum))
-- do v3..?

import PlutusCore.Version (plcVersion110)
import Ledger (minAdaTxOutEstimated)
import Plutus.Script.Utils.Ada qualified as Ada


{-
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatum))
import PlutusLedgerApi.V3 (Datum (Datum))
import PlutusLedgerApi.V3.Contexts (valuePaidTo)
-}


type Deadline = Integer

data Label = Holding
           | Collecting Value PaymentPubKeyHash Deadline [PaymentPubKeyHash]
       deriving (Show)


{-# INLINABLE lEq #-}
lEq :: Label -> Label -> Bool
lEq Holding Holding = True
lEq Holding (Collecting _ _ _ _) = False
lEq (Collecting _ _ _ _) Holding = False
lEq (Collecting v pkh d sigs) (Collecting v' pkh' d' sigs') = v == v' && pkh == pkh' && d == d' && sigs == sigs'


instance Eq Label where
    {-# INLINABLE (==) #-}
    b == c = lEq b c


data State = State
    { label  :: Label
    , tToken :: AssetClass
    } deriving (Show)

instance Eq State where
    {-# INLINABLE (==) #-}
    b == c = (label b  == label c) &&
             (tToken b == tToken c)


data Input = Propose Value PaymentPubKeyHash Deadline
           | Add PaymentPubKeyHash
           | Pay
           | Cancel
           | Close
          deriving (Show)


PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input
PlutusTx.unstableMakeIsData ''State
PlutusTx.makeLift ''State


data Params = Params {authSigs :: [PaymentPubKeyHash], nr :: Integer}
    deriving (Show)

PlutusTx.unstableMakeIsData ''Params -- ?
PlutusTx.makeLift ''Params


{-# INLINABLE query #-}
query :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || (query pkh l')

{-# INLINABLE insert #-}
insert :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> [PaymentPubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if pkh == x then x : l' else x : insert pkh l'

{-
{-# INLINABLE count #-}
count :: [PaymentPubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l-}

{-# INLINABLE lovelaceValue #-}
-- | A 'Value' containing the given quantity of Lovelace.
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken


{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))
--getLovelace . fromValue


{-# INLINABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac

minValue :: Value
minValue = lovelaceValue (Ada.getLovelace minAdaTxOutEstimated)

justLovelace :: Value -> Value
justLovelace = V.lovelaceValue . V.lovelaceValueOf

------------------------------------------------------------------------------------------------------------------------------
-- on-chain
------------------------------------------------------------------------------------------------------------------------------


{-# INLINABLE info #-}
-- ?? needed?
info :: ScriptContext -> TxInfo
info ctx = scriptContextTxInfo ctx

{-# INLINABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput ctx = case findOwnInput ctx of
        Nothing -> traceError "state input missing"
        Just i  -> txInInfoResolved i

{-# INLINABLE ownOutput #-}
ownOutput :: ScriptContext -> TxOut
ownOutput ctx = case getContinuingOutputs ctx of
        [o] -> o
        _   -> traceError "expected exactly one SM output"

{-# INLINABLE stopsCont #-}
stopsCont :: ScriptContext -> Bool
stopsCont ctx = case getContinuingOutputs ctx of
        [] -> True
        _   -> False  

{-# INLINABLE smDatum #-}
smDatum :: Maybe Datum -> Maybe State
smDatum md = do
    Datum d <- md
    PlutusTx.fromBuiltinData d

{-# INLINABLE outputDatum #-}
outputDatum :: ScriptContext -> State
outputDatum ctx = case txOutDatum (ownOutput ctx) of
        NoOutputDatum-> traceError "nt"
        OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
            Nothing -> traceError "hs"
            Just d  -> d
        OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINABLE newLabel #-}
newLabel :: ScriptContext -> Label
newLabel ctx = label (outputDatum ctx)

{-# INLINABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = justLovelace (txOutValue (ownInput ctx) <> (negate minValue))

{-# INLINABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = justLovelace (txOutValue (ownOutput ctx) <> (negate minValue))

{-# INLINABLE expired #-}
expired :: Deadline -> ScriptContext -> Bool
expired d ctx = Interval.before ((POSIXTime {getPOSIXTime = d})) (txInfoValidRange (scriptContextTxInfo ctx))

{-# INLINABLE checkSigned #-}
checkSigned :: PaymentPubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) (unPaymentPubKeyHash pkh)

{-# INLINABLE checkPayment #-}
checkPayment :: PaymentPubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = case filter (\i -> (txOutAddress i == (pubKeyHashAddress (unPaymentPubKeyHash pkh)))) (txInfoOutputs (scriptContextTxInfo ctx)) of
    os -> any (\o -> txOutValue o == v) os

-- <> (lovelaceValue minVal)


data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = State



{-# INLINABLE agdaValidator #-}
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx
  = case dat of
        Holding -> case red of
                       Propose v pkh d -> newValue ctx == oldValue ctx &&
                                            geq (oldValue ctx) v &&
                                              geq v minValue &&
                                                case newLabel ctx of
                                                    Holding -> False
                                                    Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                     pkh == pkh' &&
                                                                                       d == d' &&
                                                                                         sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False
                       Close -> stopsCont ctx && gt minValue (oldValue ctx) --gt minValue (oldValue ctx) && stopsCont ctx
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> newValue ctx == oldValue ctx &&
                                                    checkSigned sig ctx &&
                                                      query sig (authSigs param) &&
                                                        case newLabel ctx of
                                                            Holding -> False
                                                            Collecting v' pkh' d' sigs' -> v == v'
                                                                                             &&
                                                                                             pkh ==
                                                                                               pkh'
                                                                                               &&
                                                                                               d ==
                                                                                                 d'
                                                                                                 &&
                                                                                                 sigs'
                                                                                                   ==
                                                                                                   insert
                                                                                                     sig
                                                                                                     sigs
                                       Pay -> length sigs >= nr param &&
                                                case newLabel ctx of
                                                    Holding -> checkPayment pkh v ctx &&
                                                                 oldValue ctx == newValue ctx + v &&
                                                                   checkSigned pkh ctx
                                                    Collecting _ _ _ _ -> False
                                       Cancel -> newValue ctx == oldValue ctx &&
                                                   case newLabel ctx of
                                                       Holding -> expired d ctx
                                                       Collecting _ _ _ _ -> False
                                       Close -> False

{-
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param oldLabel red ctx
  = case oldLabel of
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> checkSigned sig ctx &&
                                                    query sig (authSigs param) &&
                                                      case newLabel ctx of
                                                          Holding -> False
                                                          Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                           pkh ==
                                                                                             pkh'
                                                                                             &&
                                                                                             d == d'
                                                                                               &&
                                                                                               sigs'
                                                                                                 ==
                                                                                                 insert
                                                                                                   sig
                                                                                                   sigs
                                       Pay -> count sigs >= nr param &&
                                                case newLabel ctx of
                                                    Holding -> checkPayment pkh v
                                                                 (scriptContextTxInfo ctx)
                                                                 && oldValue ctx == newValue ctx <> v
                                                    Collecting _ _ _ _ -> False
                                       Cancel -> case newLabel ctx of
                                                     Holding -> expired d (scriptContextTxInfo ctx)
                                                     Collecting _ _ _ _ -> False
        Holding -> case red of
                       Propose v pkh d -> geq (oldValue ctx) v &&
                                            case newLabel ctx of
                                                Holding -> False
                                                Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                 pkh == pkh' &&
                                                                                   d == d' &&
                                                                                     sigs' == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False-}



--SM Validator
{-# INLINABLE mkValidator #-}
mkValidator :: Params -> State -> Input -> ScriptContext -> Bool
mkValidator param st red ctx = 

    traceIfFalse "tmi" (getVal (ownInput ctx) (tToken st)  == 1)                       &&
    traceIfFalse "fv" (agdaValidator param (label st) red ctx)                         &&
	(case red of 
	  Close -> traceIfFalse "nS" (stopsCont ctx)
	  _ -> traceIfFalse "tmo" (getVal (ownOutput ctx) (tToken st) == 1) )
   -- traceIfFalse "token missing from output" ((stopsCont ctx) || (getVal (ownOutput ctx) (tToken st) == 1)) &&



smTypedValidator :: Params -> V3.TypedValidator MultiSig
smTypedValidator = go
  where
    go =
      V3.mkTypedValidatorParam @MultiSig
        $$(PlutusTx.compile [||mkValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input


mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkOtherAddress :: Params -> Address
mkOtherAddress = V3.validatorAddress . smTypedValidator


-- Thread Token
{-# INLINABLE mkPolicy #-}
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx 
    | amt == 1  = traceIfFalse "nU"   hasUTxO    &&
                  traceIfFalse "nI" checkDatum   &&
                  traceIfFalse "nD" checkValue
    | amt == -1 = traceIfFalse "contract not stopped" noOutput
    | otherwise = traceError "wO"

{-
case checkMintedAmount of
    Nothing -> traceIfFalse "wrong amount minted" False
    Just True -> traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                 traceIfFalse "not initial state" checkDatum  
    Just False -> traceIfFalse "token not burned" checkBurn

traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                          traceIfFalse "wrong amount minted" checkMintedAmount        &&
                          traceIfFalse "not initial state" checkDatum  -}
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx
    
    cs :: CurrencySymbol
    cs = ownCurrencySymbol ctx

    hasUTxO :: Bool
    hasUTxO = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs info

    amt :: Integer
    amt = case flattenValue (txInfoMint info) of
        [(_, tn', a)] 
            | tn' == tn -> a
            | otherwise -> 0 
        _               -> 0

    noOutput :: Bool
    noOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
        [] -> True
        _  -> False

{-
    checkMintedAmount :: Maybe Bool
    checkMintedAmount = case flattenValue (txInfoMint info) of
        [(_, tn', amt)] -> case tn' == tn of 
            True -> case amt of
                1  -> Just True
                (-1) -> Just False
                _  -> Nothing
            False -> Nothing
        _               -> Nothing-}
      
    scriptOutput :: TxOut
    scriptOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
    	[o] -> o
    	_ -> traceError "nU"
    
    checkDatum :: Bool
    checkDatum = case txOutDatum scriptOutput of 
        NoOutputDatum-> traceError "nd"
        OutputDatumHash dh -> case smDatum $ findDatum dh info of
            Nothing -> traceError "nh"
            Just d  -> tToken d == AssetClass (cs, tn) && label d == Holding
        OutputDatum dat -> case PlutusTx.unsafeFromBuiltinData @State (getDatum dat) of
            d -> tToken d == AssetClass (cs, tn) && label d == Holding 
            _ -> traceError "?"

    checkValue :: Bool
    checkValue = valueOf (txOutValue scriptOutput) cs tn == 1

--((txOutValue scriptOutput) == ((lovelaceValueOf minVal) <> (singleton cs tn 1)))



policy :: Params -> TxOutRef -> TokenName -> V3.MintingPolicy
policy p oref tn = Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ mkPolicy addr' oref' tn' ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 (mkOtherAddress p)
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 tn

{-
mScript :: Params -> TxOutRef -> TokenName -> SerialisedScript
mScript p oref tn = $$(PlutusTx.compile [|| \addr' oref' tn' -> mkPolicy addr' oref' tn' ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 (mkOtherAddress p)
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 tn -}

versionedPolicy :: Params -> TxOutRef -> TokenName -> Scripts.Versioned V3.MintingPolicy
versionedPolicy p oref tn = (Ledger.Versioned (policy p oref tn) Ledger.PlutusV3)

curSymbol' :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol' p oref tn = Ledger.scriptCurrencySymbol (versionedPolicy p oref tn)

curSymbol :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol p oref tn = V3.scriptCurrencySymbol (policy p oref tn)

mintingHash' :: Params -> TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash' p oref tn = Ledger.mintingPolicyHash (versionedPolicy p oref tn)

mintingHash :: Params -> TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash p oref tn = V3.mintingPolicyHash (policy p oref tn)

getPid :: Params -> TxOutRef -> TokenName -> Ledger.PolicyId
getPid p oref tn = Ledger.policyId (versionedPolicy p oref tn)

--policyId :: V3.MintingPolicy -> Ledger.PolicyId
--policyId (Ledger.MintingPolicy mp) = C.scriptPolicyId (V3.toCardanoApiScript mp)

--policyID :: Params -> TxOutRef -> TokenName -> Ledger.PolicyId
--policyID p oref tn = Ledger.policyId (policy p oref tn)

{--}


covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||mkValidator||])


