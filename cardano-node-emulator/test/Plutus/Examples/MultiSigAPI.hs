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
{-# OPTIONS_GHC -g -fplugin-opt PlutusTx.Plugin:coverage-all #-}

-- | A general-purpose escrow contract in Plutus
module Plutus.Examples.MultiSigAPI (

  -- * Actions
  propose,
  add,
  pay,
  cancel,
  start,
  TxSuccess (..),
  mkStartTx',

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
import Plutus.Script.Utils.Value --(Value, geq, lt)
import PlutusLedgerApi.V1.Interval qualified as Interval

import PlutusLedgerApi.V1.Address
import PlutusLedgerApi.V3 hiding (TxId)--(Datum (Datum))
import PlutusLedgerApi.V3.Contexts hiding (TxId)--(valuePaidTo)
import PlutusLedgerApi.V2.Tx hiding (TxId)--(OutputDatum (OutputDatum))
{-
import PlutusLedgerApi.V2.Tx (OutputDatum (OutputDatum))
import PlutusLedgerApi.V3 (Datum (Datum))
import PlutusLedgerApi.V3.Contexts (valuePaidTo)
-}

import Plutus.Examples.MultiSig
import Ledger.Address (toWitness)
import Plutus.Script.Utils.V1.Scripts qualified as Script
--import Cardano.Ledger.Alonzo.Plutus.TxInfo (transPolicyID)



toTxOutValue :: Value -> C.TxOutValue C.ConwayEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

toPolicyId :: Ledger.MintingPolicyHash -> Ledger.PolicyId
toPolicyId = either (error . show) id . C.toCardanoPolicyId

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

{-
mkTxOutput :: EscrowTarget Datum -> C.TxOut C.CtxTx C.ConwayEra
mkTxOutput = \case
  PaymentPubKeyTarget pkh vl ->
    C.TxOut
      ( C.makeShelleyAddressInEra
          C.shelleyBasedEra
          testnet
          (either (error . show) C.PaymentCredentialByKey $ C.toCardanoPaymentKeyHash pkh)
          C.NoStakeAddress
      )
      (toTxOutValue vl)
      C.TxOutDatumNone
      C.ReferenceScriptNone
  ScriptTarget (Ledger.ValidatorHash vs) ds vl ->
    C.TxOut
      ( C.makeShelleyAddressInEra
          C.shelleyBasedEra
          testnet
          (either (error . show) C.PaymentCredentialByScript $ C.toCardanoScriptHash $ Ledger.ScriptHash vs)
          C.NoStakeAddress
      )
      (toTxOutValue vl)
      (toTxOutInlineDatum ds)
      C.ReferenceScriptNone-}

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




alwaysSucceedPolicy :: V3.MintingPolicy
alwaysSucceedPolicy =
  Ledger.MintingPolicy (C.fromCardanoPlutusScript $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)

alwaysSucceedPolicyId :: C.PolicyId
alwaysSucceedPolicyId =
  C.scriptPolicyId
    (C.PlutusScript C.PlutusScriptV1 $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)

someTokenValue :: C.AssetName -> Integer -> C.Value
someTokenValue an i = C.valueFromList [(C.AssetId alwaysSucceedPolicyId an, C.Quantity i)]

threadTokenValue :: Params -> TxOutRef -> TokenName -> C.AssetName ->  C.Value
threadTokenValue p oref tn an = C.valueFromList [(C.AssetId (getPid p oref tn) an, C.Quantity 1)]
{-
curSymbol2 :: CurrencySymbol
curSymbol2 = transPolicyID alwaysSucceedPolicyId-}

mkStartTx''
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStartTx'' params wallet v tt = do

  slotConfig <- asks pSlotConfig
  unspentOutputs <- E.utxosAt wallet
  uO <- E.utxosAtPlutus wallet

  let oref = head (Map.keys uO)
  --this is probably wrong, but find some way to get a single utxo out
  
  let utxos = Map.toList (C.unUTxO unspentOutputs)
  
  when (length (utxos) == 0)
    $ throwError $ E.CustomError $ "no UTxOs" 
  
  let utxo = head utxos
  {-case Map.toList (C.unUTxO unspentOutputs) of
              [] -> throwError $ E.CustomError $ "no UTxOs" 
              x:_ -> x-}

  let tn = "ThreadToken"
      an = "ThreadToken"
      cs = curSymbol params oref tn
      tt = assetClass cs tn

  let smAddress = mkAddress params
      txOut = C.TxOut smAddress (toTxOutValue (v <> assetClassValue tt 1)) 
              (toTxOutInlineDatum (State {label = Holding, tToken = tt})) C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always
-- probably use some helper functions from https://github.com/IntersectMBO/cardano-node-emulator/blob/1e09173b74064bd5990d2d3e48af6510780ea349/plutus-ledger/src/Ledger/Tx/CardanoAPI.hs#L55
      
  --mintAmount <- toInteger <$> Gen.int (Range.linear 0 maxBound)
  --mintTokenName <- Gen.genAssetName
  let mintValue = threadTokenValue params oref tn an
      mintValue' = someTokenValue "Thread" 1
      mintValue2 = someTokenValue "asdf" 1
      redeemer = Redeemer (toBuiltinData ())
  
  -- PlutusScriptWitness :: forall lang era witctx. ScriptLanguageInEra lang era -> PlutusScriptVersion lang -> PlutusScriptOrReferenceInput lang -> 
	-- ScriptDatum witctx -> ScriptRedeemer -> ExecutionUnits -> ScriptWitness witctx era	
  
  let mintWitness = either (error . show) id $ C.toCardanoMintWitness redeemer Nothing (Just (versionedPolicy params oref tn))
      mintWitness' = either (error . show) id $ C.toCardanoMintWitness redeemer Nothing (Just (Ledger.Versioned alwaysSucceedPolicy Ledger.PlutusV1))
      mintWitness2 =
        C.PlutusScriptWitness
          C.PlutusScriptV1InConway
          C.PlutusScriptV1
          (C.PScript $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)
          C.NoScriptDatumForMint
          (C.unsafeHashableScriptData $ C.fromPlutusData $ toData () )
          C.zeroExecutionUnits
      mintWitness3 =
        C.PlutusScriptWitness
          C.PlutusScriptV1InConway
          C.PlutusScriptV1
		  
		  (C.PScript $ C.PlutusScriptSerialised (Ledger.unScript (Ledger.getMintingPolicy (policy params oref tn))))
		  
          --(C.PScript $ Ledger.unScript (Ledger.getMintingPolicy (policy params oref tn)))
          --(C.PScript $ Script.toCardanoApiScript (policy params oref tn))
          C.NoScriptDatumForMint
          (C.unsafeHashableScriptData $ C.fromPlutusData $ toData () )
          C.zeroExecutionUnits
  let txMintValue = 
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue)
          (C.BuildTxWith (Map.singleton (getPid params oref tn) mintWitness))  
      txMintValue' =  
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue')
          (C.BuildTxWith (Map.singleton alwaysSucceedPolicyId mintWitness))  
      txMintValue2 =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue2)
          (C.BuildTxWith (Map.singleton alwaysSucceedPolicyId mintWitness2))  
      txMintValue3 =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue)
          (C.BuildTxWith (Map.singleton (getPid params oref tn) mintWitness))  
	

--TxMintValue :: forall era build. MaryEraOnwards era -> Value -> BuildTxWith build (Map PolicyId (ScriptWitness WitCtxMint era)) -> TxMintValue build era	

      {-placeholder = Map.singleton (Ledger.policyId 
                    (Ledger.Versioned (policy params (C.fromCardanoTxIn (fst utxo)) "ThreadToken") Ledger.PlutusV2)) 
                    scriptWitnessPlaceholder-}
      --mint = C.TxMintValue C.MaryEraOnwardsConway (toLedgerValue (assetClassValue tt 1)) (C.BuildTxWith placeholder)
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txMintValue = txMintValue3
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in pure (C.CardanoBuildTx utx, utxoIndex)
   
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


  let mintValue2 = someTokenValue "asdf" 1

  let smAddress = mkAddress params
      txOut = C.TxOut smAddress (toTxOutValue (v <> assetClassValue tt 1 )) -- <> (C.fromCardanoValue mintValue2)) )
              (toTxOutInlineDatum (State {label = Holding, tToken = tt})) C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.always
-- probably use some helper functions from https://github.com/IntersectMBO/cardano-node-emulator/blob/1e09173b74064bd5990d2d3e48af6510780ea349/plutus-ledger/src/Ledger/Tx/CardanoAPI.hs#L55
      
  --mintAmount <- toInteger <$> Gen.int (Range.linear 0 maxBound)
  --mintTokenName <- Gen.genAssetName
  
  let mintWitness2 =
        C.PlutusScriptWitness
          C.PlutusScriptV1InConway
          C.PlutusScriptV1
          (C.PScript $ C.examplePlutusScriptAlwaysSucceeds C.WitCtxMint)
          C.NoScriptDatumForMint
          (C.unsafeHashableScriptData $ C.fromPlutusData $ toData () )
          C.zeroExecutionUnits
  let txMintValue2 =
        C.TxMintValue
          C.MaryEraOnwardsConway
          (mintValue2)
          (C.BuildTxWith (Map.singleton alwaysSucceedPolicyId mintWitness2))  
	  
      {-placeholder = Map.singleton (Ledger.policyId 
                    (Ledger.Versioned (policy params (C.fromCardanoTxIn (fst utxo)) "ThreadToken") Ledger.PlutusV2)) 
                    scriptWitnessPlaceholder-}
      --mint = C.TxMintValue C.MaryEraOnwardsConway (toLedgerValue (assetClassValue tt 1)) (C.BuildTxWith placeholder)
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          --, C.txMintValue = txMintValue2
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in pure (C.CardanoBuildTx utx, utxoIndex)

{-
mkStartTx
  :: SlotConfig
  -> Params
  -> Value
  -> AssetClass
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
  
  mkStartTx'
  :: (E.MonadEmulator m)
  => Params
  -> Ledger.CardanoAddress
  -> Value
  -> AssetClass
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)-}
  
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
  (utx, utxoIndex) <- mkStartTx'' params wallet v tt
  --let (utx, utxoIndex) = mkStartTx slotConfig params v tt
  void $ E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx


{-
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
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [toWitness privateKey] utx-}

newtype TxSuccess = TxSuccess TxId
  deriving (Eq, Show)

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
	{-( show (map (\(C.TxOut _aie tov _tod _rs) -> 
            tov ) $ Map.elems (C.unUTxO unspentOutputs) )))-}
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

