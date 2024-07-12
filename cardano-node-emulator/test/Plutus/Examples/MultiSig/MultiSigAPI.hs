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
{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

module Plutus.Examples.MultiSigAPI (

  -- * Actions
  propose,
  add,
  pay,
  cancel,
  start,
  TxSuccess (..),
 
) where

import Control.Lens (makeClassyPrisms)
import Control.Monad (void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex)
import PlutusTx.Prelude (traceError, traceIfFalse)
import PlutusTx.Prelude qualified as PlutusTx


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
import Ledger.Tx.CardanoAPI qualified as C
import Ledger.Typed.Scripts (validatorCardanoAddress)
import Ledger.Typed.Scripts qualified as Scripts
import Plutus.Script.Utils.Scripts (ValidatorHash, datumHash)
import Plutus.Script.Utils.V2.Contexts (
  ScriptContext (ScriptContext, scriptContextTxInfo),
  TxInfo,
  scriptOutputsAt,
  txInfoValidRange,
  txSignedBy,
 )
import Plutus.Script.Utils.V2.Typed.Scripts qualified as V2
import Plutus.Script.Utils.Value --(Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval
--import PlutusLedgerApi.V1.Tx
import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V2 hiding (TxId)--(Datum (Datum))
import PlutusLedgerApi.V2.Contexts hiding (TxId)--(valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId)--(OutputDatum (OutputDatum))

import Plutus.Examples.MultiSig
import Ledger.Address (toWitness)


toTxOutValue :: Value -> C.TxOutValue C.ConwayEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

toLedgerValue :: Value -> Ledger.Value
toLedgerValue = either (error . show) id . C.toCardanoValue

toHashableScriptData :: (PlutusTx.ToData a) => a -> C.HashableScriptData
toHashableScriptData = C.unsafeHashableScriptData . C.fromPlutusData . PlutusTx.toData

toTxOutInlineDatum :: (PlutusTx.ToData a) => a -> C.TxOutDatum C.CtxTx C.ConwayEra
toTxOutInlineDatum = C.TxOutDatumInline C.BabbageEraOnwardsConway . toHashableScriptData


toValidityRange
  :: SlotConfig
  -> Interval.Interval POSIXTime
  -> (C.TxValidityLowerBound C.ConwayEra, C.TxValidityUpperBound C.ConwayEra)
toValidityRange slotConfig =
  either (error . show) id . C.toCardanoValidityRange . posixTimeRangeToContainedSlotRange slotConfig


{-UTxO 
{unUTxO = 
  fromList [(TxIn \"200d08bbe612b7f6eb1b3ea8a10d2cb712a323f63dc1d5d7739dbffa63dd11df\" (TxIx 0),
  TxOut (AddressInEra (ShelleyAddressInEra ShelleyBasedEraBabbage) 
  (ShelleyAddress Testnet (ScriptHashObj 
  (ScriptHash \"a3a789420a1f12675405b95f8b56ff76af44a4e01b98a0096bc198ee\")) StakeRefNull)) 
  (TxOutValueShelleyBased ShelleyBasedEraBabbage 
  (MaryValue (Coin 100000000) (MultiAsset (fromList [])))) 
  (TxOutDatumInline BabbageEraOnwardsBabbage 
  (HashableScriptData \"\\216y\\159\\216y\\128\\216y\\159X\\FS\\199\\201\\134O\\204w\\155Us\
  \217~;\\238\\254]\\211p[\\191\\228\\EMr\\172\\217\\187n\\190\\158KThreadToken\\255\\255\" 
  (ScriptDataConstructor 0 [ScriptDataConstructor 0 [],ScriptDataConstructor 0 
  [ScriptDataBytes \"\\199\\201\\134O\\204w\\155Us\\217~;\\238\\254]\\211p[\\191
  \\228\\EMr\\172\\217\\187n\\190\\158\",ScriptDataBytes \"ThreadToken\"]])))
   ReferenceScriptNone)]}"
-}


mkProposeTx
  :: (E.MonadEmulator m)
  => Params
  -> Value
  -> PaymentPubKeyHash
  -> Deadline
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkProposeTx params val pkh d tt = do
  let smAddress = mkAddress params
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs' =
          Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
            (assetClassValueOf (C.fromCardanoValue (C.fromCardanoTxOutValue tov)) 
            tt == 1)) $ C.unUTxO unspentOutputs
            
  {-when (length (validUnspentOutputs') /= 1)
    $ throwError $ E.CustomError $ "not SM" -}
  when (length (validUnspentOutputs') == 0)
    $ throwError $ E.CustomError $ ("found no SM but: " ++ (show unspentOutputs))
  when (length (validUnspentOutputs') > 1)
    $ throwError $ E.CustomError $ "found too many SM"
  let
    --currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs')
    datum = State {label = Collecting val pkh d [], tToken = tt}
    --newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $ 
    --            (State {label = Collecting val pkh d [], tToken = tt})
        -- get actual datum!!
    remainingOutputs = [ C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone ]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Propose val pkh d)
    witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    
    txIns = (,witness) <$> Map.keys validUnspentOutputs'

    utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          , C.txOuts = remainingOutputs
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      in
        pure (C.CardanoBuildTx utx, unspentOutputs)


newtype TxSuccess = TxSuccess TxId
  deriving (Eq, Show)


propose
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> Value
  -> PaymentPubKeyHash
  -> Deadline
  -> AssetClass
  -> m TxSuccess
propose wallet privateKey params val pkh d tt = do
  E.logInfo @String "Proposing"
  (utx, utxoIndex) <- mkProposeTx params val pkh d tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


cardanoTxOutDatum :: forall d. (FromData d) => C.TxOut C.CtxUTxO C.ConwayEra -> Maybe d
cardanoTxOutDatum (C.TxOut _aie _tov tod _rs) =
  case tod of
    C.TxOutDatumNone ->
      Nothing
    C.TxOutDatumHash _era _scriptDataHash ->
      Nothing
    C.TxOutDatumInline _era scriptData ->
      fromData @d $ C.toPlutusData $ C.getScriptData scriptData

mkAddTx
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkAddTx params wallet tt = do
  let smAddress = mkAddress params
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
          Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
            (assetClassValueOf (C.fromCardanoValue (C.fromCardanoTxOutValue tov)) 
            tt == 1)) $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1)
    $ throwError $ E.CustomError $ "not SM" 
  let
    --currentlyLocked = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs)) --old
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
    datums = map (cardanoTxOutDatum @State) (Map.elems validUnspentOutputs)
    datum = case datums of
                    (Just (State {label = Collecting v pkh' d sigs, tToken = tt})) : _ -> 
                        State {label = Collecting v pkh' d (insert pkh sigs), tToken = tt}
                    otherwise -> State {label = Holding, tToken = tt} 

    --datum = State {label = Holding, tToken = tt}
    --newDatum = C.unsafeHashableScriptData $ C.fromPlutusData $ PlutusTx.toData $ 
    --            (State {label = Collecting val pkh d [], tToken = tt})
        -- get actual datum!!
    remainingOutputs = [ C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone ]

    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Add pkh)
    witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    
    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          , C.txOuts = remainingOutputs
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsConway [extraKeyWit]
          }
      in
        pure (C.CardanoBuildTx utx, unspentOutputs)


add
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
add wallet privateKey params tt = do
  E.logInfo @String "Adding"
  (utx, utxoIndex) <- mkAddTx params wallet tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


toPkhAddress :: PaymentPubKeyHash -> Ledger.CardanoAddress
toPkhAddress pkh = C.makeShelleyAddressInEra 
                    C.shelleyBasedEra
                    testnet
                    (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash pkh)
                    C.NoStakeAddress
      

mkPayTx
  :: (E.MonadEmulator m)
  => Params
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkPayTx params tt = do
  let smAddress = mkAddress params
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
          Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
            (assetClassValueOf (C.fromCardanoValue (C.fromCardanoTxOutValue tov)) 
            tt == 1)) $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1)
    $ throwError $ E.CustomError $ "not SM" 
  let
    currentValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    datums = map (cardanoTxOutDatum @State) (Map.elems validUnspentOutputs)
    (datum, (v, pkh)) = case datums of
                    (Just (State {label = Collecting v pkh d sigs, tToken = tt})) : _ -> 
                        ((State {label = Holding, tToken = tt}), (v, pkh))
                    otherwise -> ((State {label = Holding, tToken = tt}), (mempty, pkh))
    remainingOutputs = [ C.TxOut smAddress (toTxOutValue (currentValue <> (PlutusTx.negate v))) (toTxOutInlineDatum datum) C.ReferenceScriptNone ,
                         C.TxOut (toPkhAddress pkh) (toTxOutValue v) C.TxOutDatumNone C.ReferenceScriptNone] 
    validityRange = toValidityRange slotConfig $ Interval.from current
    redeemer = toHashableScriptData (Pay)
    witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs

    utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          , C.txOuts = remainingOutputs
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      in
        pure (C.CardanoBuildTx utx, unspentOutputs)


pay
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
pay wallet privateKey params tt = do
  E.logInfo @String "Paying"
  (utx, utxoIndex) <- mkPayTx params tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


mkCancelTx
  :: (E.MonadEmulator m)
  => Params
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkCancelTx params tt = do
  let smAddress = mkAddress params
  unspentOutputs <- E.utxosAt smAddress
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  let
    validUnspentOutputs =
          Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
            (assetClassValueOf (C.fromCardanoValue (C.fromCardanoTxOutValue tov)) 
            tt == 1)) $ C.unUTxO unspentOutputs
  when (length (validUnspentOutputs) /= 1)
    $ throwError $ E.CustomError $ "not SM" 
  let
    remainingValue = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue validUnspentOutputs)
    datums = map (cardanoTxOutDatum @State) (Map.elems validUnspentOutputs)
    (datum, d) = case datums of
                    (Just (State {label = Collecting v pkh d' sigs, tToken = tt})) : _ -> 
                        ((State {label = Holding, tToken = tt}), d')
                    otherwise -> ((State {label = Holding, tToken = tt}), 0)

    remainingOutputs = [ C.TxOut smAddress (toTxOutValue remainingValue) (toTxOutInlineDatum datum) C.ReferenceScriptNone ]

    validityRange = toValidityRange slotConfig $ Interval.from (POSIXTime (d + 1000)) --{getPOSIXTime = d})
    redeemer = toHashableScriptData (Cancel)
    witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
    witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
          witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
    txIns = (,witness) <$> Map.keys validUnspentOutputs
    utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          , C.txOuts = remainingOutputs
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      in
        pure (C.CardanoBuildTx utx, unspentOutputs)


cancel
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> AssetClass
  -> m TxSuccess
cancel wallet privateKey params tt = do
  E.logInfo @String "Cancelling"
  (utx, utxoIndex) <- mkCancelTx params tt
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx

-- either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

-- mint

mkStartTx'
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStartTx' params wallet v tt = do

  slotConfig <- asks pSlotConfig
  unspentOutputs <- E.utxosAt wallet

  --this is probably wrong, but find some way to get a single utxo out
  
  let utxos = Map.toList (C.unUTxO unspentOutputs)
  
  when (length (utxos) == 0)
    $ throwError $ E.CustomError $ "no UTxOs" 
  
  let utxo = head utxos
  {-case Map.toList (C.unUTxO unspentOutputs) of
              [] -> throwError $ E.CustomError $ "no UTxOs" 
              x:_ -> x-}

  let smAddress = mkAddress params
      txOut = C.TxOut smAddress (toTxOutValue v) 
              (toTxOutInlineDatum (State {label = Holding, tToken = tt})) C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always
-- probably use some helper functions from https://github.com/IntersectMBO/cardano-node-emulator/blob/1e09173b74064bd5990d2d3e48af6510780ea349/plutus-ledger/src/Ledger/Tx/CardanoAPI.hs#L55
      scriptWitnessPlaceholder = 
        C.PlutusScriptWitness
          C.PlutusScriptV1InConway
          C.PlutusScriptV1
          (C.PScript $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)
          C.NoScriptDatumForMint
          (C.unsafeHashableScriptData $ C.fromPlutusData $ toData () )
          C.zeroExecutionUnits
      
      {-placeholder = Map.singleton (Ledger.policyId 
                    (Ledger.Versioned (policy params (C.fromCardanoTxIn (fst utxo)) "ThreadToken") Ledger.PlutusV2)) 
                    scriptWitnessPlaceholder-}
      --mint = C.TxMintValue C.MaryEraOnwardsConway (toLedgerValue (assetClassValue tt 1)) (C.BuildTxWith placeholder)
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          --, C.txMintValue = mint
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in pure (C.CardanoBuildTx utx, utxoIndex)

-- (C.PolicyId (Ledger.getMintingPolicyHash (mintingHash params (C.fromCardanoTxIn (fst utxo)) "ThreadToken")))

{-
m(TxOut, TokenName)
(resultTxOut , resultTokenName) <- genAction
registerTxIn <- resultTxOut
registerToken <- resultToken
-}

mkStartTx
  :: SlotConfig
  -> Params
  -> Value
  -> AssetClass
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStartTx slotConfig params v tt =
  let smAddress = mkAddress params
      txOut = C.TxOut smAddress (toTxOutValue (v <> assetClassValue tt 1)) 
              (toTxOutInlineDatum (State {label = Holding, tToken = tt})) C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)

start
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> Params
  -> Value
  -> AssetClass
  -> m ()
start wallet privateKey params v tt = do
  E.logInfo @String $ "Starting"
  slotConfig <- asks pSlotConfig
  let (utx, utxoIndex) = mkStartTx slotConfig params v tt
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


--covIdx :: CoverageIndex
--covIdx = getCovIdx $$(PlutusTx.compile [||mkValidator||])

