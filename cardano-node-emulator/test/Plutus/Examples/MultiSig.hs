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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- {-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

-- {-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:conservative-optimisation #-}

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

  -- * testing
) where

-- writeSMValidator,
-- test,
-- test2,
-- writeCcode,
-- writeCcodePar,
-- ccode,
-- ccodePar,
-- goldenPirReadable,
-- runTestNested,
-- runTestNestedIn,
-- printPir,
-- toUPlc,
-- getPlcNoAnn,
-- writePir,
-- writeUplc,

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

-- import PlutusTx.Prelude ()
-- import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Prelude
import Prelude (IO, Show (..), String, writeFile)

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
import Plutus.Script.Utils.V3.Scripts qualified as V3
import Plutus.Script.Utils.V3.Typed.Scripts qualified as V3
import Plutus.Script.Utils.Value -- (Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval

import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V1.Value qualified as V

-- (Datum (Datum))
-- (valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId) -- (OutputDatum (OutputDatum))
-- do v3..?

import PlutusLedgerApi.V3 hiding (TxId)
import PlutusLedgerApi.V3.Contexts hiding (TxId)

import Codec.Serialise (serialise)
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Short qualified as SBS
import Ledger (minAdaTxOutEstimated)
import Plutus.Script.Utils.Ada qualified as Ada
import PlutusCore.Version (plcVersion110)

import PlutusCore.Test
import PlutusTx.Test
import Test.Tasty.Extras

-- (prettyPirReadableSimple)

import Control.Exception
import Control.Lens (Getting, traverseOf, view)
import Control.Monad.Except (ExceptT, catchError, liftEither, runExceptT, throwError, withExceptT)
import Flat (Flat)
import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Pretty qualified as PLC
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type (progTerm)
import PlutusTx.Code (CompiledCode, CompiledCodeIn, getPir, getPirNoAnn, getPlcNoAnn, sizePlc)
import Prettyprinter qualified
import Test.Tasty.Extras (TestNested, nestedGoldenVsDoc, testNested)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

{--}
{-
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatum))
import PlutusLedgerApi.V3 (Datum (Datum))
import PlutusLedgerApi.V3.Contexts (valuePaidTo)
-}

type Deadline = Integer

data Label
  = Holding
  | Collecting Value PaymentPubKeyHash Deadline [PaymentPubKeyHash]
  deriving (Show)

{-# INLINEABLE lEq #-}
lEq :: Label -> Label -> Bool
lEq Holding Holding = True
lEq Holding (Collecting _ _ _ _) = False
lEq (Collecting _ _ _ _) Holding = False
lEq (Collecting v pkh d sigs) (Collecting v' pkh' d' sigs') = v == v' && pkh == pkh' && d == d' && sigs == sigs'

instance Eq Label where
  {-# INLINEABLE (==) #-}
  b == c = lEq b c

data State = State
  { label :: Label
  , tToken :: AssetClass
  }
  deriving (Show)

instance Eq State where
  {-# INLINEABLE (==) #-}
  b == c =
    (label b == label c)
      && (tToken b == tToken c)

data Input
  = Propose Value PaymentPubKeyHash Deadline
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

{-# INLINEABLE query #-}
query :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || (query pkh l')

{-# INLINEABLE insert #-}
insert :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> [PaymentPubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l') =
  if pkh == x then x : l' else x : insert pkh l'

{-
{-# INLINABLE count #-}
count :: [PaymentPubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l-}

{-# INLINEABLE lovelaceValue #-}

-- | A 'Value' containing the given quantity of Lovelace.
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken

{-# INLINEABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces v = assetClassValueOf v (AssetClass (adaSymbol, adaToken))

-- getLovelace . fromValue

{-# INLINEABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac

minValue :: Value
minValue = lovelaceValue (Ada.getLovelace minAdaTxOutEstimated)

justLovelace :: Value -> Value
justLovelace = V.lovelaceValue . V.lovelaceValueOf

------------------------------------------------------------------------------------------------------------------------------
-- on-chain
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE info #-}
-- ?? needed?
info :: ScriptContext -> TxInfo
info ctx = scriptContextTxInfo ctx

{-# INLINEABLE ownInput #-}
ownInput :: ScriptContext -> TxOut
ownInput ctx = case findOwnInput ctx of
  Nothing -> error ()
  Just i -> txInInfoResolved i

{-# INLINEABLE ownOutput #-}
ownOutput :: ScriptContext -> TxOut
ownOutput ctx = case getContinuingOutputs ctx of
  [o] -> o
  _ -> error ()

{-# INLINEABLE stopsCont #-}
stopsCont :: ScriptContext -> Bool
stopsCont ctx = case getContinuingOutputs ctx of
  [] -> True
  _ -> False

{-# INLINEABLE smDatum #-}
smDatum :: Maybe Datum -> Maybe State
smDatum md = do
  Datum d <- md
  PlutusTx.fromBuiltinData d

{-# INLINEABLE outputDatum #-}
outputDatum :: ScriptContext -> State
outputDatum ctx = case txOutDatum (ownOutput ctx) of
  NoOutputDatum -> error ()
  OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
    Nothing -> error ()
    Just d -> d
  OutputDatum d -> PlutusTx.unsafeFromBuiltinData (getDatum d)

{-# INLINEABLE newLabel #-}
newLabel :: ScriptContext -> Label
newLabel ctx = label (outputDatum ctx)

{-# INLINEABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = justLovelace (txOutValue (ownInput ctx) <> (negate minValue))

{-# INLINEABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = justLovelace (txOutValue (ownOutput ctx) <> (negate minValue))

{-# INLINEABLE expired #-}
expired :: Deadline -> ScriptContext -> Bool
expired d ctx = Interval.before ((POSIXTime{getPOSIXTime = d})) (txInfoValidRange (scriptContextTxInfo ctx))

{-

To ensure that a deadline (I assume it's store din a datum for the next validator) is at most a week from now on chain you need:
Put an upper bound on the transaction t_max and check t_max + (7*24*60*60*1000) = deadline
Put a lower bound on the transaction t_min and check that t_max - t_min is within a reasonable time frame, e.g. 1 hour: t_max - t_min < (60*60*1000)
Off-chain you then need to select an upper bound slot and compute the offset (1 week) of it, which you can then use as a deadline in the datum.
This will result in a deadline being maximum 1 week + 1 hour away from now

asdf :: POSIXTime
asdf = getPOSIXTime
-}
{-# INLINEABLE checkSigned #-}
checkSigned :: PaymentPubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) (unPaymentPubKeyHash pkh)

{-# INLINEABLE checkPayment #-}
checkPayment :: PaymentPubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = case filter
  (\i -> (txOutAddress i == (pubKeyHashAddress (unPaymentPubKeyHash pkh))))
  (txInfoOutputs (scriptContextTxInfo ctx)) of
  os -> any (\o -> txOutValue o == v) os

-- <> (lovelaceValue minVal)

data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = State

{-# INLINEABLE agdaValidator #-}
agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx =
  case dat of
    Holding -> case red of
      Propose v pkh d ->
        newValue ctx
          == oldValue ctx
          && geq (oldValue ctx) v
          && geq v minValue
          && case newLabel ctx of
            Holding -> False
            Collecting v' pkh' d' sigs' -> v == v' && pkh == pkh' && d == d' && sigs' == []
      Add _ -> False
      Pay -> False
      Cancel -> False
      Close -> stopsCont ctx && gt minValue (oldValue ctx)
    Collecting v pkh d sigs -> case red of
      Propose _ _ _ -> False
      Add sig ->
        newValue ctx
          == oldValue ctx
          && checkSigned sig ctx
          && query sig (authSigs param)
          && case newLabel ctx of
            Holding -> False
            Collecting v' pkh' d' sigs' -> v == v' && pkh == pkh' && d == d' && sigs' == insert sig sigs
      Pay ->
        length sigs >= nr param && case newLabel ctx of
          Holding -> checkPayment pkh v ctx && oldValue ctx == newValue ctx + v && checkSigned pkh ctx
          Collecting _ _ _ _ -> False
      Cancel ->
        newValue ctx == oldValue ctx && case newLabel ctx of
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

-- 44323
-- 43241
-- SM Validator
{-# INLINEABLE mkValidator #-}
mkValidator :: Params -> State -> Input -> ScriptContext -> Bool
mkValidator param st red ctx =
  (getVal (ownInput ctx) (tToken st) == 1)
    && (agdaValidator param (label st) red ctx)
    && ( case red of
          Close -> (stopsCont ctx)
          _ -> (getVal (ownOutput ctx) (tToken st) == 1)
       )

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
{-# INLINEABLE mkPolicy #-}
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx
  | amt == 1 =
      hasUTxO
        && checkDatum
        && checkValue
  | amt == -1 = noOutput
  | otherwise = error ()
  where
    {-
    case checkMintedAmount of
        Nothing -> traceIfFalse "wrong amount minted" False
        Just True -> traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                     traceIfFalse "not initial state" checkDatum
        Just False -> traceIfFalse "token not burned" checkBurn

    traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                              traceIfFalse "wrong amount minted" checkMintedAmount        &&
                              traceIfFalse "not initial state" checkDatum  -}

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
      _ -> 0

    noOutput :: Bool
    noOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
      [] -> True
      _ -> False

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
      _ -> error ()

    checkDatum :: Bool
    checkDatum = case txOutDatum scriptOutput of
      NoOutputDatum -> error ()
      OutputDatumHash dh -> case smDatum $ findDatum dh info of
        Nothing -> error ()
        Just d -> tToken d == AssetClass (cs, tn) && label d == Holding
      OutputDatum dat -> case PlutusTx.unsafeFromBuiltinData @State (getDatum dat) of
        d -> tToken d == AssetClass (cs, tn) && label d == Holding
        _ -> error ()

    checkValue :: Bool
    checkValue = valueOf (txOutValue scriptOutput) cs tn == 1

-- ((txOutValue scriptOutput) == ((lovelaceValueOf minVal) <> (singleton cs tn 1)))

policy :: Params -> TxOutRef -> TokenName -> V3.MintingPolicy
policy p oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ mkPolicy addr' oref' tn'||]
        )
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

-- policyId :: V3.MintingPolicy -> Ledger.PolicyId
-- policyId (Ledger.MintingPolicy mp) = C.scriptPolicyId (V3.toCardanoApiScript mp)

-- policyID :: Params -> TxOutRef -> TokenName -> Ledger.PolicyId
-- policyID p oref tn = Ledger.policyId (policy p oref tn)

{--}

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||mkValidator||])

modelParams' :: Params
modelParams' =
  Params
    { authSigs =
        []
    , nr = 2
    }

{-
ccode :: PlutusTx.CompiledCode (Params -> State -> Input -> ScriptContext -> Bool)
ccode = $$(PlutusTx.compile [||mkValidator||])

ccodePar :: PlutusTx.CompiledCode (State -> Input -> ScriptContext -> Bool)
ccodePar =
  $$( PlutusTx.compile
        [||\params' -> mkValidator params'||]
    )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 modelParams'

test :: SerialisedScript
test = serialiseCompiledCode ccode

test2 :: SerialisedScript
test2 = serialiseCompiledCode ccodePar

serialisedNP :: C.PlutusScript C.PlutusScriptV3
serialisedNP = C.PlutusScriptSerialised test

serialisedPar :: C.PlutusScript C.PlutusScriptV3
serialisedPar = C.PlutusScriptSerialised test2

writeCcode :: IO ()
writeCcode = void $ C.writeFileTextEnvelope "ccode.plutus" Nothing serialisedNP

writeCcodePar :: IO ()
writeCcodePar = void $ C.writeFileTextEnvelope "ccodePar.plutus" Nothing serialisedPar

testValidator :: V3.Validator
testValidator = Scripts.validatorScript (smTypedValidator modelParams')

smScript :: Ledger.Script
smScript = Ledger.unValidatorScript testValidator

shortSMS :: SBS.ShortByteString
shortSMS = SBS.toShort . LBS.toStrict $ serialise smScript

smsv2 :: C.PlutusScript C.PlutusScriptV3
smsv2 = C.PlutusScriptSerialised shortSMS

writeSMValidator :: IO ()
writeSMValidator = void $ C.writeFileTextEnvelope "whole.plutus" Nothing smsv2

printPir :: PlutusTx.CompiledCode a -> Doc b
printPir c = (prettyPirReadable (view progTerm (fromJust (getPirNoAnn c))))

writePir :: IO ()
writePir = writeFile "pir.txt" (show (printPir ccode))

writeUplc :: IO ()
writeUplc = writeFile "uplc.txt" (show (getPlcNoAnn ccode)) -}

{-
printUplc :: PlutusTx.CompiledCode a -> Doc b
printUplc c = withExceptT @_ @UPLC.FreeVariableError toException $ traverseOf UPLC.progTerm UPLC.deBruijnTerm (runExceptT (toUPlc c))
-}
{-
goldenPirReadable ::
  (PrettyUni uni, Pretty fun, uni `PLC.Everywhere` Flat, Flat fun) =>
  String ->
  CompiledCodeIn uni fun a ->
  TestNested
goldenPirReadable name value =
  nestedGoldenVsDoc name ".pir"
    . maybe "PIR not found in CompiledCode" (prettyPirReadable . view progTerm)
    $ getPirNoAnn value-}

{-
writeSMValidator :: Bool
writeSMValidator = True-}
{-}
pkhh :: PaymentPubKeyHash
pkhh = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e"

modelParams' :: Params
modelParams' =
  Params
    { authSigs = [pkhh, pkhh, pkhh]
    , nr = 2
    }

aaaaa :: Params -> PlutusTx.CompiledCode a
aaaaa = $$(PlutusTx.compile [||mkValidator||])

test :: SerialisedScript
test = serialiseCompiledCode (smTypedValidator modelParams')-}
-- ,
--  serialiseUPLC
