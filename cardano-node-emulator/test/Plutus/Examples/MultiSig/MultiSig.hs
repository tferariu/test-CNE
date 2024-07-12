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

module Plutus.Examples.MultiSig (
  -- $escrow
  State (..),
  Params (..),
{--}
  smTypedValidator,
  mkAddress,
  insert,
{-
  -- * Actions
  propose,
  add,
  pay,
  cancel,
  start,
  TxSuccess (..),
  -}
  -- * Exposed for test endpoints
  Input (..),
  Datum,
  Deadline,
  Label (..),
  mkValidator,
  mkPolicy,
  --policy,
  --curSymbol,
  --mintingHash,

  -- * Coverage
  covIdx, 
) where

import Control.Lens (makeClassyPrisms)
import Control.Monad (void, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.RWS.Class (asks)
import Data.Map qualified as Map

import Data.Set qualified as Set
--import PlutusCore qualified

import Cardano.Api qualified as C
import Cardano.Api.Shelley qualified as C
import PlutusTx (ToData)
import PlutusTx qualified
import PlutusTx.Code (getCovIdx)
import PlutusTx.Coverage (CoverageIndex, addCoverageMetadata, Metadata(..))
import PlutusTx.Prelude (traceError, traceIfFalse)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Prelude --(Eq, Bool, Integer)
--import PlutusTx

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

import           Prelude              (Show (..), String)

--import PlutusCore.Version (plcVersion100)

minVal :: Integer --Lovelace
minVal = 2000000


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
          deriving (Show)


PlutusTx.unstableMakeIsData ''Label
PlutusTx.makeLift ''Label
PlutusTx.unstableMakeIsData ''Input
PlutusTx.makeLift ''Input
PlutusTx.unstableMakeIsData ''State
PlutusTx.makeLift ''State




{-# INLINABLE query #-}
query :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || (query pkh l')

{-# INLINABLE insert #-}
insert :: PaymentPubKeyHash -> [PaymentPubKeyHash] -> [PaymentPubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if x == pkh then x : l' else x : insert pkh l'

{-# INLINABLE count #-}
count :: [PaymentPubKeyHash] -> Integer
count [] = 0
count (x : l) = 1 + count l

data Params = Params {authSigs :: [PaymentPubKeyHash], nr :: Integer}
    deriving (Show)

PlutusTx.unstableMakeIsData ''Params
PlutusTx.makeLift ''Params




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
oldValue ctx = txOutValue (ownInput ctx)

{-# INLINABLE newValue #-}
newValue :: ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

{-# INLINABLE expired #-}
expired :: Deadline -> TxInfo -> Bool
expired d info = Interval.before ((POSIXTime {getPOSIXTime = d})) (txInfoValidRange info)

{-# INLINABLE checkSigned #-}
checkSigned :: PaymentPubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = txSignedBy (scriptContextTxInfo ctx) (unPaymentPubKeyHash pkh)

{-# INLINABLE checkPayment #-}
checkPayment :: PaymentPubKeyHash -> Value -> TxInfo -> Bool
checkPayment pkh v info = case filter (\i -> (txOutAddress i == (pubKeyHashAddress (unPaymentPubKeyHash pkh)))) (txInfoOutputs info) of
    os -> any (\o -> txOutValue o == v) os

-- <> (lovelaceValue minVal)

{-# INLINABLE agdaValidator #-}
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
                       Cancel -> False


--SM Validator
{-# INLINABLE mkValidator #-}
mkValidator :: Params -> State -> Input -> ScriptContext -> Bool
mkValidator param st red ctx =

    traceIfFalse "token missing from input" (getVal (ownInput ctx) (tToken st)  == 1)                 &&
    traceIfFalse "token missing from output" (getVal (ownOutput ctx) (tToken st) == 1)                &&
    traceIfFalse "failed Validation" (agdaValidator param (label st) red ctx)

{-(case (agdaValidator param (label st) red ctx) of 
      True -> True
      False -> (traceError "failed Validation"))-}
--traceIfFalse "failed validation" False --

data MultiSig
instance Scripts.ValidatorTypes MultiSig where
  type RedeemerType MultiSig = Input
  type DatumType MultiSig = State


smTypedValidator :: Params -> V2.TypedValidator MultiSig
smTypedValidator = go
  where
    go =
      V2.mkTypedValidatorParam @MultiSig
        $$(PlutusTx.compile [||mkValidator||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator -- @ScriptContext @State @Input

mkAddress :: Params -> Ledger.CardanoAddress
mkAddress = validatorCardanoAddress testnet . smTypedValidator

mkOtherAddress :: Params -> Address
mkOtherAddress = V2.validatorAddress . smTypedValidator

covIdx :: CoverageIndex
covIdx = getCovIdx $$(PlutusTx.compile [||mkValidator||])

-- Thread Token
{-# INLINABLE mkPolicy #-}
mkPolicy :: Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
mkPolicy addr oref tn () ctx = traceIfFalse "UTxO not consumed"   hasUTxO                  &&
                          traceIfFalse "wrong amount minted" checkMintedAmount        &&
                          traceIfFalse "not initial state" checkDatum  
  where
    info :: TxInfo
    info = scriptContextTxInfo ctx
    
    cs :: CurrencySymbol
    cs = ownCurrencySymbol ctx

    hasUTxO :: Bool
    hasUTxO = any (\i -> txInInfoOutRef i == oref) $ txInfoInputs info

    checkMintedAmount :: Bool
    checkMintedAmount = case flattenValue (txInfoMint info) of
        [(_, tn', amt)] -> tn' == tn && amt == 1
        _               -> False
      
    scriptOutput :: TxOut
    scriptOutput = case filter (\i -> (txOutAddress i == (addr))) (txInfoOutputs info) of
    	[o] -> o
    	_ -> traceError "not unique SM output"
    
    checkDatum :: Bool
    checkDatum = case txOutDatum scriptOutput of 
        NoOutputDatum-> traceError "nd"
        OutputDatumHash dh -> case smDatum $ findDatum dh info of
            Nothing -> traceError "nh"
            Just d  -> tToken d == AssetClass (cs, tn) && label d == Holding
        OutputDatum dat -> case PlutusTx.unsafeFromBuiltinData @State (getDatum dat) of
            d -> tToken d == AssetClass (cs, tn) && label d == Holding 
            _ -> traceError "?"

{-
policy :: Params -> TxOutRef -> TokenName -> V2.MintingPolicy
policy p oref tn = Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ mkPolicy addr' oref' tn' ||])
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 (mkOtherAddress p)
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 oref
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 tn


curSymbol :: Params -> TxOutRef -> TokenName -> CurrencySymbol
curSymbol p oref tn = Ledger.scriptCurrencySymbol $ (Ledger.Versioned (policy p oref tn) Ledger.PlutusV2)

mintingHash :: Params -> TxOutRef -> TokenName -> Ledger.MintingPolicyHash
mintingHash p oref tn = Ledger.mintingPolicyHash $ (Ledger.Versioned (policy p oref tn) Ledger.PlutusV2)-}

{-

mkMintingPolicy :: () -> ScriptContext -> Bool
mkMintingPolicy _ _ = True

validator :: V2.MintingPolicy
validator = Ledger.mkMintingPolicyScript
     $$(PlutusTx.compile [|| wrap ||])
  where
     wrap = Scripts.mkUntypedMintingPolicy mkMintingPolicy


mkForwardingMintingPolicy :: ValidatorHash -> MintingPolicy
mkForwardingMintingPolicy vshsh =
  mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||
            \(hsh :: ValidatorHash) ->
              mkUntypedMintingPolicy (forwardToValidator hsh)
            ||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 vshsh-}


  --   
  --
  --   validator :: Plutus.Validator
  --   validator = Plutus.mkMintingPolicyScript
  --       $$(PlutusTx.compile [|| wrap ||])
  --    where
  --       wrap = mkUntypedMintingPolicy mkMintingPolicy

{-

mkMintingPolicyScript :: CompiledCode (BuiltinData -> BuiltinData -> ()) -> MintingPolicy
mkMintingPolicyScript = MintingPolicy . Script . serialiseCompiledCode

-- | Make a 'TypedValidator' from the 'CompiledCode' of a validator script and its wrapper.
mkTypedValidator
  :: CompiledCode (ValidatorType a)
  -- ^ Validator script (compiled)
  -> CompiledCode (ValidatorType a -> UntypedValidator)
  -- ^ A wrapper for the compiled validator
  -> TypedValidator a
mkTypedValidator vc wrapper =
  TypedValidator
    { tvValidator = Versioned val PlutusV2
    , tvValidatorHash = hsh
    , tvForwardingMPS = Versioned mps PlutusV2
    , tvForwardingMPSHash = Scripts.mintingPolicyHash mps
    }
  where
    val = mkValidatorScript $ wrapper `unsafeApplyCode` vc
    hsh = Scripts.validatorHash val
    mps = MPS.mkForwardingMintingPolicy hsh

-- | Make a 'TypedValidator' from the 'CompiledCode' of a parameterized validator script and its wrapper.
mkTypedValidatorParam
  :: forall a param
   . (Lift DefaultUni param)
  => CompiledCode (param -> ValidatorType a)
  -- ^ Validator script (compiled)
  -> CompiledCode (ValidatorType a -> UntypedValidator)
  -- ^ A wrapper for the compiled validator
  -> param
  -- ^ The extra paramater for the validator script
  -> TypedValidator a
mkTypedValidatorParam vc wrapper param =
  mkTypedValidator (vc `unsafeApplyCode` liftCode plcVersion100 param) wrapper


mkForwardingMintingPolicy :: ValidatorHash -> MintingPolicy
mkForwardingMintingPolicy vshsh =
  mkMintingPolicyScript
    $ $$( PlutusTx.compile
            [||
            \(hsh :: ValidatorHash) ->
              mkUntypedMintingPolicy (forwardToValidator hsh)
            ||]
        )
    `PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 vshsh

`PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 (mkAddress p)
`PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 oref
`PlutusTx.unsafeApplyCode` PlutusTx.liftCode plcVersion100 tn

{-# INLINEABLE forwardToValidator #-}
forwardToValidator :: ValidatorHash -> () -> PV2.ScriptContext -> Bool
forwardToValidator (ValidatorHash h) _ ScriptContext{scriptContextTxInfo = TxInfo{txInfoInputs}, scriptContextPurpose = Minting _} =
  let checkHash TxOut{txOutAddress = Address{addressCredential = ScriptCredential (ScriptHash vh)}} = vh == h
      checkHash _ = False
   in any (checkHash . PV2.txInInfoResolved) txInfoInputs
forwardToValidator _ _ _ = False

policy :: Params -> TxOutRef -> TokenName -> Scripts.MintingPolicy
policy p oref tn = Ledger.mkMintingPolicyScript $
    $$(PlutusTx.compile [|| \addr' oref' tn' -> Scripts.mkUntypedMintingPolicy $ mkPolicy addr' oref' tn' ||])
    `PlutusTx.applyCode`
    PlutusTx.liftCode plcVersion100 (mkAddress p)
    `PlutusTx.applyCode`
    PlutusTx.liftCode plcVersion100 oref
    `PlutusTx.applyCode`
    PlutusTx.liftCode plcVersion100 tn
 

curSymbol :: TxOutRef -> TokenName -> CurrencySymbol
curSymbol oref tn = Scripts.scriptCurrencySymbol $ policy oref tn
-}


{-
allNonFailLocations :: HasCallStack => PlutusTx.CompiledCodeIn PlutusCore.DefaultUni PlutusCore.DefaultFun a -> Set CoverageAnnotation
allNonFailLocations = uncurry allLocations . interpCode

computeRefinedCoverageIndex :: PlutusTx.CompiledCodeIn PlutusCore.DefaultUni PlutusCore.DefaultFun a -> CoverageIndex
computeRefinedCoverageIndex cc =
    foldr (flip addCoverageMetadata IgnoredAnnotation) covIdx (Set.toList ignoredLocs)
  where
    covIdx        = getCovIdx cc
    importantLocs = allNonFailLocations cc
    ignoredLocs   = covIdx ^. coverageMetadata . to Map.keysSet . to (`Set.difference` importantLocs)

covIdx :: CoverageIndex
covIdx = computeRefinedCoverageIndex $$(PlutusTx.compile [|| \a b c d -> check (mkValidator a b c d) ||])-}


-------------------------------------------------------------------------

{-
show' :: C.ToCardanoError -> ()
show' s = ()
-}
{-
toTxOutValue :: Value -> C.TxOutValue C.BabbageEra
toTxOutValue = either (error . show) C.toCardanoTxOutValue . C.toCardanoValue

toHashableScriptData :: (PlutusTx.ToData a) => a -> C.HashableScriptData
toHashableScriptData = C.unsafeHashableScriptData . C.fromPlutusData . PlutusTx.toData

toTxOutInlineDatum :: (PlutusTx.ToData a) => a -> C.TxOutDatum C.CtxTx C.BabbageEra
toTxOutInlineDatum = C.TxOutDatumInline C.BabbageEraOnwardsBabbage . toHashableScriptData

toValidityRange
  :: SlotConfig
  -> Interval.Interval POSIXTime
  -> (C.TxValidityLowerBound C.BabbageEra, C.TxValidityUpperBound C.BabbageEra)
toValidityRange slotConfig =
  either (error . show) id . C.toCardanoValidityRange . posixTimeRangeToContainedSlotRange slotConfig

{--}
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
  when (length (validUnspentOutputs') /= 1)
    $ throwError $ E.CustomError $ "not SM" 
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
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx


cardanoTxOutDatum :: forall d. (FromData d) => C.TxOut C.CtxUTxO C.BabbageEra -> Maybe d
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
          , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsBabbage [extraKeyWit]
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
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx


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
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx


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

    validityRange = toValidityRange slotConfig $ Interval.from (POSIXTime d) --{getPOSIXTime = d})
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
  TxSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx


-- | Pay some money into the escrow contract.
mkStartTx
  :: SlotConfig
  -> Params
  -> Value
  -> AssetClass
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkStartTx slotConfig params v tt =
  let smAddress = mkAddress params
      txOut = C.TxOut smAddress (toTxOutValue v) (toTxOutInlineDatum (State {label = Holding, tToken = tt})) C.ReferenceScriptNone
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
  void $ E.submitTxConfirmed utxoIndex wallet [privateKey] utx

-}


{-
-----------------------------------------------------------------

data RedeemFailReason = DeadlinePassed | NotEnoughFundsAtAddress
  deriving stock (Eq, Show)

data EscrowError
  = RedeemFailed RedeemFailReason
  | RefundFailed
  deriving stock (Show)

makeClassyPrisms ''EscrowError

{- $escrow
The escrow contract implements the exchange of value between multiple
parties. It is defined by a list of targets (public keys and script
addresses, each associated with a value). It works similar to the
crowdfunding contract in that the contributions can be made independently,
and the funds can be unlocked only by a transaction that pays the correct
amount to each target. A refund is possible if the outputs locked by the
contract have not been spent by the deadline. (Compared to the crowdfunding
contract, the refund policy is simpler because here because there is no
"collection period" during which the outputs may be spent after the deadline
has passed. This is because we're assuming that the participants in the
escrow contract will make their deposits as quickly as possible after
agreeing on a deal)
-}

{- | Defines where the money should go. Usually we have `d = Datum` (when
  defining `EscrowTarget` values in off-chain code). Sometimes we have
  `d = DatumHash` (when checking the hashes in on-chain code)
-}
data EscrowTarget d
  = PaymentPubKeyTarget PaymentPubKeyHash Value
  | ScriptTarget ValidatorHash d Value
  deriving (Functor)

PlutusTx.makeLift ''EscrowTarget

-- | An 'EscrowTarget' that pays the value to a public key address.
payToPaymentPubKeyTarget :: PaymentPubKeyHash -> Value -> EscrowTarget d
payToPaymentPubKeyTarget = PaymentPubKeyTarget

{- | An 'EscrowTarget' that pays the value to a script address, with the
  given data script.
-}
payToScriptTarget :: ValidatorHash -> Datum -> Value -> EscrowTarget Datum
payToScriptTarget = ScriptTarget

-- | Definition of an escrow contract, consisting of a deadline and a list of targets
data EscrowParams d = EscrowParams
  { escrowDeadline :: POSIXTime
  -- ^ Latest point at which the outputs may be spent.
  , escrowTargets :: [EscrowTarget d]
  -- ^ Where the money should go. For each target, the contract checks that
  --   the output 'mkTxOutput' of the target is present in the spending
  --   transaction.
  }
  deriving (Functor)

PlutusTx.makeLift ''EscrowParams

{- | The total 'Value' that must be paid into the escrow contract
  before it can be unlocked
-}
targetTotal :: EscrowParams d -> Value
targetTotal = foldl (\vl tgt -> vl <> targetValue tgt) mempty . escrowTargets

-- | The 'Value' specified by an 'EscrowTarget'
targetValue :: EscrowTarget d -> Value
targetValue = \case
  PaymentPubKeyTarget _ vl -> vl
  ScriptTarget _ _ vl -> vl


-- | Create a 'Ledger.TxOut' value for the target
mkTxOutput :: EscrowTarget Datum -> C.TxOut C.CtxTx C.BabbageEra
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
      C.ReferenceScriptNone

data Action = Redeem | Refund

data Escrow
instance Scripts.ValidatorTypes Escrow where
  type RedeemerType Escrow = Action
  type DatumType Escrow = PaymentPubKeyHash

PlutusTx.unstableMakeIsData ''Action
PlutusTx.makeLift ''Action

{-# INLINEABLE meetsTarget #-}

{- | @ptx `meetsTarget` tgt@ if @ptx@ pays at least @targetValue tgt@ to the
  target address.

  The reason why this does not require the target amount to be equal
  to the actual amount is to enable any excess funds consumed by the
  spending transaction to be paid to target addresses. This may happen if
  the target address is also used as a change address for the spending
  transaction, and allowing the target to be exceed prevents outsiders from
  poisoning the contract by adding arbitrary outputs to the script address.
-}
meetsTarget :: TxInfo -> EscrowTarget Datum -> Bool
meetsTarget ptx = \case
  PaymentPubKeyTarget pkh vl ->
    valuePaidTo ptx (unPaymentPubKeyHash pkh) `geq` vl
  ScriptTarget validatorHash dataValue vl ->
    case scriptOutputsAt validatorHash ptx of
      [(dataValue', vl')] ->
        PlutusTx.traceIfFalse "dataValue" (dataValue' PlutusTx.== OutputDatum dataValue)
          PlutusTx.&& PlutusTx.traceIfFalse "value" (vl' `geq` vl)
      _ -> False

{-# INLINEABLE validate #-}
validate :: EscrowParams Datum -> PaymentPubKeyHash -> Action -> ScriptContext -> Bool
validate EscrowParams{escrowDeadline, escrowTargets} contributor action ScriptContext{scriptContextTxInfo} =
  case action of
    Redeem ->
      PlutusTx.traceIfFalse
        "escrowDeadline-after"
        (escrowDeadline `Interval.after` txInfoValidRange scriptContextTxInfo)
        PlutusTx.&& PlutusTx.traceIfFalse
          "meetsTarget"
          (PlutusTx.all (meetsTarget scriptContextTxInfo) escrowTargets)
    Refund ->
      PlutusTx.traceIfFalse
        "escrowDeadline-before"
        ((escrowDeadline PlutusTx.- 1000) `Interval.before` txInfoValidRange scriptContextTxInfo)
        PlutusTx.&& PlutusTx.traceIfFalse
          "txSignedBy"
          (scriptContextTxInfo `txSignedBy` unPaymentPubKeyHash contributor)

typedValidator :: EscrowParams Datum -> V2.TypedValidator Escrow
typedValidator = go
  where
    go =
      V2.mkTypedValidatorParam @Escrow
        $$(PlutusTx.compile [||validate||])
        $$(PlutusTx.compile [||wrap||])
    wrap = Scripts.mkUntypedValidator

mkEscrowAddress :: EscrowParams Datum -> Ledger.CardanoAddress
mkEscrowAddress = validatorCardanoAddress testnet . typedValidator

-- | Pay some money into the escrow contract.
mkPayTx
  :: SlotConfig
  -> EscrowParams Datum
  -- ^ The escrow contract
  -> Ledger.CardanoAddress
  -- ^ Wallet address
  -> Value
  -- ^ How much money to pay in
  -> (C.CardanoBuildTx, Ledger.UtxoIndex)
mkPayTx slotConfig escrow wallet vl =
  let escrowAddr = mkEscrowAddress escrow
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
      txOut = C.TxOut escrowAddr (toTxOutValue vl) (toTxOutInlineDatum pkh) C.ReferenceScriptNone
      validityRange = toValidityRange slotConfig $ Interval.to $ escrowDeadline escrow - 1000
      utx =
        E.emptyTxBodyContent
          { C.txOuts = [txOut]
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          }
      utxoIndex = mempty
   in (C.CardanoBuildTx utx, utxoIndex)

pay
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> EscrowParams Datum
  -> Value
  -> m ()
pay wallet privateKey escrow vl = do
  E.logInfo @String $ "Pay " <> show vl <> " to the script"
  slotConfig <- asks pSlotConfig
  let (utx, utxoIndex) = mkPayTx slotConfig escrow wallet vl
  void $ E.submitTxConfirmed utxoIndex wallet [privateKey] utx

newtype RedeemSuccess = RedeemSuccess TxId
  deriving (Eq, Show)

{- | Redeem all outputs at the contract address using a transaction that
  has all the outputs defined in the contract's list of targets.
-}
mkRedeemTx
  :: (E.MonadEmulator m)
  => EscrowParams Datum
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkRedeemTx escrow = do
  let escrowAddr = mkEscrowAddress escrow
  unspentOutputs <- E.utxosAt escrowAddr
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange
  if current >= escrowDeadline escrow
    then throwError $ E.CustomError $ show (RedeemFailed DeadlinePassed)
    else
      if C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO unspentOutputs))
        `lt` targetTotal escrow
        then throwError $ E.CustomError $ show (RedeemFailed NotEnoughFundsAtAddress)
        else
          let
            validityRange = toValidityRange slotConfig $ Interval.to $ escrowDeadline escrow - 1000
            txOuts = map mkTxOutput (escrowTargets escrow)
            witnessHeader =
              C.toCardanoTxInScriptWitnessHeader
                (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator escrow))
            redeemer = toHashableScriptData Redeem
            witness =
              C.BuildTxWith $
                C.ScriptWitness C.ScriptWitnessForSpending $
                  witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
            txIns = (,witness) <$> Map.keys (C.unUTxO unspentOutputs)
            utx =
              E.emptyTxBodyContent
                { C.txIns = txIns
                , C.txOuts = txOuts
                , C.txValidityLowerBound = fst validityRange
                , C.txValidityUpperBound = snd validityRange
                }
           in
            pure (C.CardanoBuildTx utx, unspentOutputs)

redeem
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> EscrowParams Datum
  -> m RedeemSuccess
redeem wallet privateKey escrow = do
  E.logInfo @String "Redeeming"
  (utx, utxoIndex) <- mkRedeemTx escrow
  RedeemSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx

newtype RefundSuccess = RefundSuccess TxId
  deriving newtype (Eq, Show)

-- | Claim a refund of the contribution.
mkRefundTx
  :: (E.MonadEmulator m)
  => EscrowParams Datum
  -> Ledger.CardanoAddress
  -- ^ Wallet address
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkRefundTx escrow wallet = do
  let escrowAddr = mkEscrowAddress escrow
  unspentOutputs <- E.utxosAt escrowAddr
  slotConfig <- asks pSlotConfig
  let validityRange = toValidityRange slotConfig $ Interval.from $ escrowDeadline escrow
      pkh = Ledger.PaymentPubKeyHash $ fromJust $ Ledger.cardanoPubKeyHash wallet
      extraKeyWit = either (error . show) id $ C.toCardanoPaymentKeyHash pkh
      pkhDatumHash = datumHash $ Datum $ PlutusTx.toBuiltinData pkh
      ownUnspentOutputs =
        Map.keys $
          Map.filter (\(C.TxOut _aie _tov tod _rs) -> C.fromCardanoTxOutDatumHash' tod == Just pkhDatumHash) $
            C.unUTxO unspentOutputs
      witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator escrow))
      redeemer = toHashableScriptData Refund
      witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
      txIns = (,witness) <$> ownUnspentOutputs
      utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          , C.txValidityLowerBound = fst validityRange
          , C.txValidityUpperBound = snd validityRange
          , C.txExtraKeyWits = C.TxExtraKeyWitnesses C.AlonzoEraOnwardsBabbage [extraKeyWit]
          }
  if null txIns
    then throwError $ E.CustomError $ show RefundFailed
    else pure (C.CardanoBuildTx utx, unspentOutputs)

refund
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> EscrowParams Datum
  -> m RefundSuccess
refund wallet privateKey escrow = do
  E.logInfo @String "Refunding"
  (utx, utxoIndex) <- mkRefundTx escrow wallet
  RefundSuccess . getCardanoTxId <$> E.submitTxConfirmed utxoIndex wallet [privateKey] utx

-- Submit a transaction attempting to take the refund belonging to the given pk.
mkBadRefundTx
  :: (E.MonadEmulator m)
  => EscrowParams Datum
  -> Ledger.PaymentPubKeyHash
  -> m (C.CardanoBuildTx, Ledger.UtxoIndex)
mkBadRefundTx escrow pkh = do
  let escrowAddr = mkEscrowAddress escrow
  unspentOutputs <- E.utxosAt escrowAddr
  let pkhDatumHash = datumHash $ Datum $ PlutusTx.toBuiltinData pkh
      pkhUnspentOutputs =
        Map.keys $
          Map.filter (\(C.TxOut _aie _tov tod _rs) -> C.fromCardanoTxOutDatumHash' tod == Just pkhDatumHash) $
            C.unUTxO unspentOutputs
      witnessHeader =
        C.toCardanoTxInScriptWitnessHeader
          (Ledger.getValidator <$> Scripts.vValidatorScript (typedValidator escrow))
      redeemer = toHashableScriptData Refund
      witness =
        C.BuildTxWith $
          C.ScriptWitness C.ScriptWitnessForSpending $
            witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
      txIns = (,witness) <$> pkhUnspentOutputs
      utx =
        E.emptyTxBodyContent
          { C.txIns = txIns
          }
  pure (C.CardanoBuildTx utx, unspentOutputs)

badRefund
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> EscrowParams Datum
  -> Ledger.PaymentPubKeyHash
  -> m ()
badRefund wallet privateKey escrow pkh = do
  E.logInfo @String "Bad refund"
  (utx, utxoIndex) <- mkBadRefundTx escrow pkh
  (void $ E.submitTxConfirmed utxoIndex wallet [privateKey] utx)
    `catchError` (\err -> E.logError $ "Caught error: " ++ show err)

{- | Pay some money into the escrow contract. Then release all funds to their
  specified targets if enough funds were deposited before the deadline,
  or reclaim the contribution if the goal has not been met.
-}
payRedeemRefund
  :: (E.MonadEmulator m)
  => Ledger.CardanoAddress
  -> Ledger.PaymentPrivateKey
  -> EscrowParams Datum
  -> Value
  -> m (Either RefundSuccess RedeemSuccess)
payRedeemRefund wallet privateKey escrow vl = do
  let escrowAddr = mkEscrowAddress escrow
      go = do
        cur <- E.utxosAt escrowAddr
        let presentVal = C.fromCardanoValue (foldMap Ledger.cardanoTxOutValue (C.unUTxO cur))
        if presentVal `geq` targetTotal escrow
          then Right <$> redeem wallet privateKey escrow
          else do
            time <- snd <$> E.currentTimeRange
            if time >= escrowDeadline escrow
              then Left <$> refund wallet privateKey escrow
              else E.nextSlot >> go
  -- Pay the value 'vl' into the contract
  void $ pay wallet privateKey escrow vl
  go


-}
{--}

{-    
  let smAddr = mkAddress params
  unspentOutputs <- E.utxosAt smAddr
  slotConfig <- asks pSlotConfig
  current <- fst <$> E.currentTimeRange

  let
            st = State
                     { label  = Collecting val pkh d []
                      , tToken = tt
                     }
            smUnspentOutputs = Map.keys $
                Map.filter (\(C.TxOut _aie tov _tod _rs) -> 
                (assetClassValueOf (C.fromCardanoValue (C.fromCardanoTxOutValue tov)) 
                tt == 1)) $ C.unUTxO unspentOutputs

            pkhDatumHash = datumHash $ Datum $ PlutusTx.toBuiltinData pkh
            ownUnspentOutputs =
                Map.keys $
                Map.filter (\(C.TxOut _aie _tov tod _rs) -> 
                C.fromCardanoTxOutDatumHash' tod == Just pkhDatumHash) $
                C.unUTxO unspentOutputs

            validityRange = toValidityRange slotConfig $ Interval.from $ current
            --txOut = C.TxOut smAddr tov (toTxOutInlineDatum st) C.ReferenceScriptNone
            witnessHeader =
              C.toCardanoTxInScriptWitnessHeader
                (Ledger.getValidator <$> Scripts.vValidatorScript (smTypedValidator params))
            redeemer = toHashableScriptData (Propose val pkh d)
            witness =
              C.BuildTxWith $
                C.ScriptWitness C.ScriptWitnessForSpending $
                  witnessHeader C.InlineScriptDatum redeemer C.zeroExecutionUnits
            txIns = (,witness) <$> smUnspentOutputs 
            utx =
              E.emptyTxBodyContent
                { C.txIns = txIns
                , C.txOuts = Map.elems (C.unUTxO unspentOutputs)
                , C.txValidityLowerBound = fst validityRange
                , C.txValidityUpperBound = snd validityRange
                }
    in case smUnspentOutputs of 
        [] -> throwError $ E.CustomError $ show "no contract"
        [x] -> pure (C.CardanoBuildTx utx, unspentOutputs)
        (x : xs) -> throwError $ E.CustomError $ show ">1 contract"
   
-}