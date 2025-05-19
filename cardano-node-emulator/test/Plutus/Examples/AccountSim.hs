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
module Plutus.Examples.AccountSim (
  -- $multisig
  AccountSim,
  State (..),
  smTypedValidator,
  mkAddress,
  insert,
  delete,
  lookup,

  -- * Exposed for test endpoints
  Input (..),
  Datum,
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

{-{-# INLINEABLE lEq #-}
lEq :: Label -> Label -> Bool
lEq Holding Holding = True
lEq Holding (Collecting _ _ _ _) = False
lEq (Collecting _ _ _ _) Holding = False
lEq (Collecting v pkh d sigs) (Collecting v' pkh' d' sigs') = v == v' && pkh == pkh' && d == d' && sigs == sigs'

instance Eq Label where
  {-# INLINEABLE (==) #-}
  b == c = lEq b c

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
-}

type Label = [(PubKeyHash, Value)]

type State = (AssetClass, Label)

data Input
  = Open PubKeyHash
  | Close PubKeyHash
  | Withdraw PubKeyHash Value
  | Deposit PubKeyHash Value
  | Transfer PubKeyHash PubKeyHash Value
  deriving (Show)

-- PlutusTx.unstableMakeIsData ''Label
-- PlutusTx.makeLift ''Label
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input

-- PlutusTx.unstableMakeIsData ''State
-- PlutusTx.makeLift ''State

{-# INLINEABLE insert #-}
insert :: PubKeyHash -> Value -> Label -> Label
insert pkh val [] = [(pkh, val)]
insert pkh val ((x, y) : xs) =
  if pkh == x then (pkh, val) : xs else (x, y) : insert pkh val xs

{-# INLINEABLE delete #-}
delete :: PubKeyHash -> Label -> Label
delete pkh [] = []
delete pkh ((x, y) : xs) =
  if pkh == x then xs else (x, y) : delete pkh xs

{-# INLINEABLE lookup #-}
lookup :: PubKeyHash -> Label -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x, y) : xs) =
  if pkh == x then Just y else lookup x xs

---- ?

{-# INLINEABLE getVal #-}
getVal :: TxOut -> AssetClass -> Integer
getVal ip ac = assetClassValueOf (txOutValue ip) ac

{-# INLINEABLE lovelaceValue #-}
lovelaceValue :: Integer -> Value
lovelaceValue = singleton adaSymbol adaToken

{-# INLINEABLE minValue #-}
minValue :: Value
minValue = lovelaceValue (Ada.getLovelace minAdaTxOutEstimated)

{-# INLINEABLE emptyValue #-}
emptyValue :: Value
emptyValue = lovelaceValue (Ada.getLovelace 0)

---- ?

------------------------------------------------------------------------------------------------------------------------------
-- on-chain for Validator
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE info #-}
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

{-# INLINEABLE continuing #-}
continuing :: ScriptContext -> Bool
continuing ctx = case getContinuingOutputs ctx of
  [o] -> True
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
newLabel ctx = snd (outputDatum ctx)

{-# INLINEABLE newToken #-}
newToken :: ScriptContext -> AssetClass
newToken ctx = fst (outputDatum ctx)

{-# INLINEABLE oldValue #-}
oldValue :: ScriptContext -> Value
oldValue ctx = txOutValue (ownInput ctx)

{-# INLINEABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

{-# INLINEABLE checkSigned #-}
checkSigned :: PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) pkh

{-# INLINEABLE checkMembership #-}
checkMembership :: Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

{-# INLINEABLE checkEmpty #-}
checkEmpty :: Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

{-# INLINEABLE checkWithdraw #-}
checkWithdraw
  :: Maybe Value
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkWithdraw Nothing _ _ _ _ = False
checkWithdraw (Just v) pkh val lab ctx =
  geq val emptyValue
    && geq v val
    && newLabel ctx
    == insert pkh (v - val) lab

{-# INLINEABLE checkDeposit #-}
checkDeposit
  :: Maybe Value
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkDeposit Nothing _ _ _ _ = False
checkDeposit (Just v) pkh val lab ctx =
  geq val emptyValue && newLabel ctx == insert pkh (v + val) lab

{-# INLINEABLE checkTransfer #-}
checkTransfer
  :: Maybe Value
  -> Maybe Value
  -> PubKeyHash
  -> PubKeyHash
  -> Value
  -> Label
  -> ScriptContext
  -> Bool
checkTransfer Nothing _ _ _ _ _ _ = False
checkTransfer (Just vF) Nothing _ _ _ _ _ = False
checkTransfer (Just vF) (Just vT) from to val lab ctx =
  geq val 0
    && geq vF val
    && from
    /= to
    && newLabel ctx
    == insert from (vF - val) (insert to (vT + val) lab)

{-# INLINEABLE checkTokenIn #-}
checkTokenIn :: AssetClass -> ScriptContext -> Bool
checkTokenIn ac ctx = getVal (ownInput ctx) ac == 1

{-# INLINEABLE checkTokenOut #-}
checkTokenOut :: AssetClass -> ScriptContext -> Bool
checkTokenOut ac ctx = getVal (ownOutput ctx) ac == 1

data AccountSim
instance Scripts.ValidatorTypes AccountSim where
  type RedeemerType AccountSim = Input
  type DatumType AccountSim = State

{-# INLINEABLE agdaValidator #-}
agdaValidator :: () -> State -> Input -> ScriptContext -> Bool
agdaValidator () (tok, lab) inp ctx =
  checkTokenIn tok ctx
    && checkTokenOut tok ctx
    && continuing ctx
    && newToken ctx
    == tok
    && case inp of
      Open pkh ->
        checkSigned pkh ctx
          && not (checkMembership (lookup pkh lab))
          && newLabel ctx
          == insert pkh 0 lab
          && newValue ctx
          == oldValue ctx
      Close pkh ->
        checkSigned pkh ctx
          && checkEmpty (lookup pkh lab)
          && newLabel ctx
          == delete pkh lab
          && newValue ctx
          == oldValue ctx
      Withdraw pkh val ->
        checkSigned pkh ctx
          && checkWithdraw (lookup pkh lab) pkh val lab ctx
          && newValue ctx
          == oldValue ctx
          - val
      Deposit pkh val ->
        checkSigned pkh ctx
          && checkDeposit (lookup pkh lab) pkh val lab ctx
          && newValue ctx
          == oldValue ctx
          + val
      Transfer from to val ->
        checkSigned from ctx
          && checkTransfer
            (lookup from lab)
            (lookup to lab)
            from
            to
            val
            lab
            ctx
          && newValue ctx
          == oldValue ctx

-- traceIfFalse "token missing from output" ((stopsCont ctx) || (getVal (ownOutput ctx) (tToken st) == 1)) &&

{-
smTypedValidator :: V3.TypedValidator AccountSim
smTypedValidator = go
  where
    go =
      V3.mkTypedValidatorParam @AccountSim
        $$(PlutusTx.compile [||agdaValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input

mkAddress :: Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkOtherAddress :: Address
mkOtherAddress = V3.validatorAddress . smTypedValidator-}

smTypedValidator :: () -> V3.TypedValidator AccountSim
smTypedValidator = go
  where
    go =
      V3.mkTypedValidatorParam @AccountSim
        $$(PlutusTx.compile [||agdaValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input

mkAddress :: Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator ()

mkOtherAddress :: Address
mkOtherAddress = V3.validatorAddress . smTypedValidator ()

------------------------------------------------------------------------------------------------------------------------------
-- on-chain for Minting Policy
------------------------------------------------------------------------------------------------------------------------------

{-# INLINEABLE getMintedAmount #-}
getMintedAmount :: ScriptContext -> Integer
getMintedAmount ctx = case flattenValue (txInfoMint (scriptContextTxInfo ctx)) of
  [(cs, _, a)]
    | cs == ownCurrencySymbol ctx -> a
    | otherwise -> 0
  _ -> 0

{-# INLINEABLE consumes #-}
consumes :: TxOutRef -> ScriptContext -> Bool
consumes oref ctx = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs (scriptContextTxInfo ctx)

{-# INLINEABLE checkDatum #-}
checkDatum :: Address -> ScriptContext -> Bool
checkDatum addr ctx = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs (scriptContextTxInfo ctx)) of
  [o] -> case txOutDatum o of
    NoOutputDatum -> False
    OutputDatumHash dh -> case smDatum $ findDatum dh (scriptContextTxInfo ctx) of
      Nothing -> False
      Just d -> d == (AssetClass (ownCurrencySymbol ctx, "ThreadToken"), []) -- tToken d == AssetClass (cs, tn) && label d == Holding
    OutputDatum dat -> case PlutusTx.unsafeFromBuiltinData @State (getDatum dat) of
      d -> d == (AssetClass (ownCurrencySymbol ctx, "ThreadToken"), []) -- tToken d == AssetClass (cs, tn) && label d == Holding
      _ -> False
  _ -> False

{-# INLINEABLE checkValue #-}
checkValue :: Address -> ScriptContext -> Bool
checkValue addr ctx = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs (scriptContextTxInfo ctx)) of
  [o] -> valueOf (txOutValue o) (ownCurrencySymbol ctx) "ThreadToken" == 1
  _ -> False

{-# INLINEABLE isInitial #-}
isInitial :: Address -> TxOutRef -> ScriptContext -> Bool
isInitial addr oref ctx =
  consumes oref ctx && checkDatum addr ctx && checkValue addr ctx

{-# INLINEABLE continuingAddr #-}
continuingAddr :: Address -> ScriptContext -> Bool
continuingAddr addr ctx = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs (scriptContextTxInfo ctx)) of
  [] -> False
  _ -> True

{-# INLINEABLE agdaPolicy #-}
agdaPolicy :: Address -> TxOutRef -> () -> ScriptContext -> Bool
agdaPolicy addr oref _ ctx =
  if amt == 1
    then continuingAddr addr ctx && isInitial addr oref ctx
    else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

policy :: TxOutRef -> TokenName -> V3.MintingPolicy
policy oref tn =
  Ledger.mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||\addr' oref' -> Scripts.mkUntypedMintingPolicy $ agdaPolicy addr' oref'||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 mkOtherAddress
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion110 oref

versionedPolicy :: TxOutRef -> TokenName -> Scripts.Versioned V3.MintingPolicy
versionedPolicy oref tn = (Ledger.Versioned (policy oref tn) Ledger.PlutusV3)

curSymbol' :: TxOutRef -> TokenName -> CurrencySymbol
curSymbol' oref tn = Ledger.scriptCurrencySymbol (versionedPolicy oref tn)

curSymbol :: TxOutRef -> TokenName -> CurrencySymbol
curSymbol oref tn = V3.scriptCurrencySymbol (policy oref tn)

mintingHash' :: TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash' oref tn = Ledger.mintingPolicyHash (versionedPolicy oref tn)

mintingHash :: TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash oref tn = V3.mintingPolicyHash (policy oref tn)

getPid :: TxOutRef -> TokenName -> Ledger.PolicyId
getPid oref tn = Ledger.policyId (versionedPolicy oref tn)

------------------------------------------------------------------------------

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||agdaValidator||])
