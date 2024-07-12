{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Plutus.Examples.MultiSigSpec (
  
  tests,
  prop_MultiSig,
  prop_Check,
  checkPropMultiSigWithCoverage,
  {-prop_Escrow_DoubleSatisfaction,
  prop_FinishEscrow,
  prop_observeEscrow,
  prop_NoLockedFunds,
  prop_validityChecks,
  checkPropEscrowWithCoverage,
  EscrowModel,
  normalCertification,
  normalCertification',
  quickCertificationWithCheckOptions,
  outputCoverageOfQuickCertification,
  runS-}
) where

import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import GHC.Generics (Generic)

import Cardano.Api.Shelley (toPlutusData)
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node.Params qualified as Params
import Cardano.Node.Emulator.Internal.Node.TimeSlot qualified as TimeSlot
import Cardano.Node.Emulator.Test (
  checkPredicateOptions,
  hasValidatedTransactionCountOfTotal,
  walletFundsChange,
  (.&&.),
 )
import Cardano.Node.Emulator.Test.Coverage (writeCoverageReport)
import Cardano.Node.Emulator.Test.NoLockedFunds (
  NoLockedFundsProof (nlfpMainStrategy, nlfpWalletStrategy),
  checkNoLockedFundsProofWithOptions,
  defaultNLFP,
 )
import Ledger (Slot, minAdaTxOutEstimated)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Value (Value, geq, TokenName, AssetClass, CurrencySymbol, assetClass, valueOf, assetClassValue)
import PlutusLedgerApi.V1.Time (POSIXTime)

import Plutus.Examples.MultiSig hiding (Input(..), Label(..))
import Plutus.Examples.MultiSigAPI (
  --Params (..),
  propose,
  add,
  pay,
  cancel,
  start,
  --typedValidator,
 )
import Plutus.Examples.MultiSig qualified as Impl

import PlutusTx (fromData)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Monoid (inv)

import Data.Maybe (fromJust)

import Cardano.Api (
  AddressInEra (AddressInEra),
  AllegraEraOnwards (AllegraEraOnwardsConway),
  IsShelleyBasedEra (shelleyBasedEra),
  TxOut (TxOut),
  TxValidityLowerBound (TxValidityLowerBound, TxValidityNoLowerBound),
  TxValidityUpperBound (TxValidityUpperBound),
  UTxO (unUTxO),
  toAddressAny,
  PolicyId (..),
  AssetName (..),
 )
import Test.QuickCheck qualified as QC hiding ((.&&.))
import Test.QuickCheck.ContractModel (
  Action,
  Actions,
  ContractModel,
  DL,
  RunModel,
  action,
  anyActions_,
  assertModel,
  contractState,
  currentSlot,
  deposit,
  forAllDL,
  lockedValue,
  observe,
  symIsZero,
  utxo,
  viewContractState,
  viewModelState,
  wait,
  waitUntilDL,
  withdraw,
 )
import Test.QuickCheck.ContractModel qualified as QCCM
import Test.QuickCheck.ContractModel.ThreatModel (
  IsInputOrOutput (addressOf),
  ThreatModel,
  anyInputSuchThat,
  changeValidityRange,
  getRedeemer,
  shouldNotValidate,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  Property,
  choose,
  frequency,
  testProperty,
  chooseInteger,
 )



curr :: CurrencySymbol
curr = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e" 

tn :: TokenName
tn = "ThreadToken"

tt :: AssetClass
tt = assetClass curr tn

type Wallet = Integer

w1, w2, w3, w4, w5 :: Wallet
w1 = 1
w2 = 2
w3 = 3
w4 = 4
w5 = 5

walletAddress :: Wallet -> Ledger.CardanoAddress
walletAddress = (E.knownAddresses !!) . pred . fromIntegral

walletPrivateKey :: Wallet -> Ledger.PaymentPrivateKey
walletPrivateKey = (E.knownPaymentPrivateKeys !!) . pred . fromIntegral

testWallets :: [Wallet]
testWallets = [w1, w2, w3, w4, w5] -- removed five to increase collisions (, w6, w7, w8, w9, w10])

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral




modelParams :: Params
modelParams = Params {authSigs = [walletPaymentPubKeyHash w4 , walletPaymentPubKeyHash w5, walletPaymentPubKeyHash w3], nr = 2}

data Phase = Initial
		   | Holding
           | Collecting 
       deriving (Show, Eq, Generic)

data MultiSigModel = MultiSigModel
  { _actualValue :: Value
  , _allowedSignatories :: [Wallet] 
  , _requiredSignatories :: Integer
  , _threadToken :: AssetClass
  , _phase :: Phase
  , _paymentValue :: Value
  , _paymentTarget :: Maybe Wallet
  , _deadline :: Maybe Integer
  , _actualSignatories :: [Wallet]
  }
  deriving (Eq, Show, Generic)

makeLenses ''MultiSigModel


options :: E.Options MultiSigModel
options =
  E.defaultOptions
    { E.initialDistribution = defInitialDist
    , E.params = Params.increaseTransactionLimits def
    , E.coverageIndex = Impl.covIdx
    }



genWallet :: QC.Gen Wallet
genWallet = QC.elements testWallets

genTT :: QC.Gen	AssetClass
genTT = QC.elements [tt]

beginningOfTime :: Integer
beginningOfTime = 1596059091000

instance ContractModel MultiSigModel where
  data Action MultiSigModel
    = Propose Wallet Value Wallet Integer
    | Add Wallet
    | Pay Wallet
    | Cancel Wallet
    | Start Wallet Value AssetClass
    deriving (Eq, Show, Generic)

  initialState =
    MultiSigModel
      { _actualValue = mempty 
      , _allowedSignatories = [w5, w3, w4]
	  , _requiredSignatories = (nr modelParams)
      , _threadToken = tt --AssetClass (adaSymbol, adaToken)
      , _phase = Initial
      , _paymentValue = mempty
      , _paymentTarget = Nothing
      , _deadline = Nothing
      , _actualSignatories = []
      
      }


-- here?
  nextState a = void $ case a of
    Propose w1 v w2 d -> do
      phase .= Collecting
      paymentValue .= v
      paymentTarget .= Just w2
--      curSlot <- viewModelState currentSlot
--      endSlot .= curSlot + deadline
      deadline .= Just d
      wait 1
    Add w -> do
      actualSignatories' <- viewContractState actualSignatories
      actualSignatories %= --(w:) 
	                       (case (elem w actualSignatories') of
                                True -> id
                                False -> (w:))
      wait 1
      {-
      actualSignatories' <- viewContractState actualSignatories
      actualSignatories’ = nub (w : actualSignatories)
      -}
    Pay w -> do
      phase .= Holding
      deadline .= Nothing
      address <- viewContractState paymentTarget
      paymentTarget .= Nothing
      actualSignatories .= []
      actualValue' <- viewContractState actualValue
      paymentValue' <- viewContractState paymentValue
      actualValue .= actualValue' <> (PlutusTx.negate paymentValue')
      deposit (walletAddress (fromJust address)) paymentValue' 
      paymentValue .= mempty
      wait 1
    Cancel w -> do
      phase .= Holding
      actualSignatories .= []
      paymentTarget .= Nothing
      paymentValue .= mempty
      deadline .= Nothing
      wait 1
    Start w v tt' -> do
      phase .= Holding
      withdraw (walletAddress w) (v <> (assetClassValue tt 1))
      actualValue .= v
      threadToken .= tt'
      wait 1



  precondition s a = case a of
			Propose w1 v w2 d -> currentPhase == Holding && (currentValue `geq` v)
			Add w -> currentPhase == Collecting && (elem w sigs) -- && not (elem w actualSigs)
			Pay w -> currentPhase == Collecting && ((length actualSigs) >= (fromIntegral min))
			Cancel w -> currentPhase == Collecting && ((d + 2000) < timeInt)
			Start w v tt' -> currentPhase == Initial
		where 
		currentPhase = s ^. contractState . phase
		currentValue = s ^. contractState . actualValue
		sigs = s ^. contractState . allowedSignatories
		actualSigs = s ^. contractState . actualSignatories
		min = s ^. contractState . requiredSignatories
		slot = s ^. currentSlot . to fromCardanoSlotNo
		time = TimeSlot.slotToBeginPOSIXTime def slot
		timeInt = Ledger.getPOSIXTime time
		d = fromJust $ (s ^. contractState . deadline)
	
{-	
    Redeem _ ->
      (s ^. contractState . contributions . to Data.Foldable.fold)
        `geq` (s ^. contractState . targets . to Data.Foldable.fold)
        && ( s ^. currentSlot . to fromCardanoSlotNo
              < s ^. contractState . refundSlot - 2
           )
    Refund w ->
      s ^. currentSlot . to fromCardanoSlotNo
        > s ^. contractState . refundSlot
        && Nothing /= (s ^. contractState . contributions . at w)
    Pay _ v ->
      s ^. currentSlot . to fromCardanoSlotNo
        < s ^. contractState . refundSlot - 2
        && Ada.adaValueOf (fromInteger v) `geq` Ada.toValue Ledger.minAdaTxOutEstimated
    BadRefund w w' ->
      s ^. currentSlot . to fromCardanoSlotNo < s ^. contractState . refundSlot - 2 -- why -2?
        || w /= w'-}


  -- enable again later
  validFailingAction _ _ = False


--put token back in Start
  arbitraryAction s = frequency [ (1 , Propose <$> genWallet
											   <*> (Ada.lovelaceValueOf
                                                   <$> choose (((Ada.getLovelace Ledger.minAdaTxOutEstimated) * 2), valueOf amount Ada.adaSymbol Ada.adaToken))
											   <*> genWallet
											   <*> chooseInteger (timeInt, timeInt + 10000))
							    , (3, Add <$> genWallet)
							    , (2, Pay <$> genWallet)
							    , (1, Cancel <$> genWallet)
							    , (1, Start <$> genWallet
										    <*> (Ada.lovelaceValueOf
                                                   <$> choose (((Ada.getLovelace Ledger.minAdaTxOutEstimated) * 2), 1000000000000))
											<*> genTT)
								]
		where
			amount   = s ^. contractState . actualValue
			slot = s ^. currentSlot . to fromCardanoSlotNo
			time = TimeSlot.slotToEndPOSIXTime def slot
			timeInt = Ledger.getPOSIXTime time
			--int' = Ledger.getSlot slot'




{-instance RunModel MultiSigModel E.EmulatorM where
  perform _ cmd _ = lift $ void $ act cmd-}

instance RunModel MultiSigModel E.EmulatorM where
  perform _ cmd _ = lift $ act cmd
  
  
currC :: Value.PolicyId
currC = PolicyId {unPolicyId = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e" }

tnC :: Value.AssetName
tnC = AssetName "ThreadToken"

defInitialDist :: Map Ledger.CardanoAddress Value.Value
defInitialDist = Map.fromList $ (, (Value.lovelaceValueOf 99999900000000000 <> 
                 Value.singleton currC tnC 1)) <$> E.knownAddresses


act :: Action MultiSigModel -> E.EmulatorM ()
act = \case
  Propose w1 v w2 d ->
    void $ 
      propose
        (walletAddress w1)
        (walletPrivateKey w1)
        modelParams
        v
        (walletPaymentPubKeyHash w2)
        d
        tt
  Add w ->
    void $
      add
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Pay w ->
    void $
      pay
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Cancel w ->
    void $
      cancel
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        tt
  Start w v tt ->
    
      start
        (walletAddress w)
        (walletPrivateKey w)
        modelParams
        v
        tt
  


prop_MultiSig :: Actions MultiSigModel -> Property
prop_MultiSig = E.propRunActionsWithOptions options


prop_Escrow_DoubleSatisfaction :: Actions MultiSigModel -> Property
prop_Escrow_DoubleSatisfaction = E.checkDoubleSatisfactionWithOptions options


simpleVestTest :: DL MultiSigModel ()
simpleVestTest = do
          action $ Start 1 (Ada.adaValueOf 100) tt
          action $ Propose 2 (Ada.adaValueOf 10) 3 111111111111111111111111111
          action $ Add 4
          action $ Add 4
          action $ Add 5
          action $ Add 4
          action $ Cancel 2
{-
observeUTxOEscrow :: DL EscrowModel ()
observeUTxOEscrow = do
  action $ Pay w1 10
  observe "After payment" $ \_ cst -> numUTxOsAt addr cst == 1
  waitUntilDL 100
  action $ Refund w1
  observe "After refund" $ \_ cst -> numUTxOsAt addr cst == 0
  where
    addr = Scripts.validatorCardanoAddressAny Params.testnet $ typedValidator modelParams

    numUTxOsAt addr cst =
      Data.Foldable.length
        [ ()
        | TxOut (AddressInEra _ addr') _ _ _ <- Map.elems . unUTxO $ utxo cst
        , toAddressAny addr' == addr
        ]

prop_observeEscrow :: Property
prop_observeEscrow = forAllDL observeUTxOEscrow prop_Escrow


prop_Check :: QC.Property
prop_Check = QC.withMaxSuccess 1 $ forAllDL simpleVestTest prop_MultiSig
-}

prop_Check :: Property
prop_Check = forAllDL simpleVestTest prop_MultiSig


{-
finishEscrow :: DL EscrowModel ()
finishEscrow = do
  anyActions_
  finishingStrategy (const True)
  assertModel "Locked funds are not zero" (symIsZero . lockedValue)

finishingStrategy :: (Ledger.CardanoAddress -> Bool) -> DL EscrowModel ()
finishingStrategy walletAlive = do
  now <- viewModelState (currentSlot . to fromCardanoSlotNo)
  slot <- viewContractState refundSlot
  when (now < slot + 1) $ waitUntilDL $ fromIntegral $ slot + 1
  contribs <- viewContractState contributions
  Data.Foldable.sequence_
    [action $ Refund w | w <- testWallets, w `Map.member` contribs, walletAlive (walletAddress w)]

prop_FinishEscrow :: Property
prop_FinishEscrow = forAllDL finishEscrow prop_Escrow

noLockProof :: NoLockedFundsProof EscrowModel
noLockProof =
  defaultNLFP
    { nlfpMainStrategy = finishingStrategy (const True)
    , nlfpWalletStrategy = finishingStrategy . (==)
    }

prop_NoLockedFunds :: Property
prop_NoLockedFunds = checkNoLockedFundsProofWithOptions options noLockProof-}

{-
-- | Check that you can't redeem after the deadline and not refund before the deadline.
validityChecks :: ThreatModel ()
validityChecks = do
  let deadline = fromIntegral . TimeSlot.posixTimeToEnclosingSlot def $ escrowDeadline modelParams
      scriptAddr = Scripts.validatorCardanoAddressAny Params.testnet $ typedValidator modelParams
  input <- anyInputSuchThat $ (scriptAddr ==) . addressOf
  rmdr <- (fromData . toPlutusData =<<) <$> getRedeemer input
  case rmdr of
    Nothing -> fail "Missing or bad redeemer"
    Just Impl.Redeem ->
      shouldNotValidate $
        changeValidityRange
          ( TxValidityLowerBound AllegraEraOnwardsConway deadline
          , TxValidityUpperBound shelleyBasedEra Nothing
          )
    Just Impl.Refund ->
      shouldNotValidate $
        changeValidityRange
          ( TxValidityNoLowerBound
          , TxValidityUpperBound shelleyBasedEra (Just $ deadline - 1)
          )

prop_validityChecks :: Actions EscrowModel -> Property
prop_validityChecks = E.checkThreatModelWithOptions options validityChecks-}




tests :: TestTree
tests =
  testGroup
    "MultiSig"
    [ checkPredicateOptions
        options
        "can start"
        ( hasValidatedTransactionCountOfTotal 1 1
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1)))
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
		  
    {-, checkPredicateOptions
        options
        "can propose"
        ( hasValidatedTransactionCountOfTotal 2 2
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            .&&. walletFundsChange (walletAddress w2) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
          --act $ Start 2 (Ada.adaValueOf 100 <> (assetClassValue tt 1))
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
    , checkPredicateOptions
        options
        "can add"
        ( hasValidatedTransactionCountOfTotal 4 4
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1)))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 4
          act $ Add 5
    , checkPredicateOptions
        options
        "can pay"
        ( hasValidatedTransactionCountOfTotal 5 5
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 5
          act $ Add 4
          act $ Pay 3
    , checkPredicateOptions
        options
        "can cancel"
        ( hasValidatedTransactionCountOfTotal 7 7
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1)))
            -- .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
          act $ Propose 2 (Ada.adaValueOf 10) 3 1596059095001
          act $ Add 4
          act $ Add 4
          act $ Add 5
          act $ Add 4
          act $ Cancel 2
    , checkPredicateOptions
        options
        "can double pay"
        ( hasValidatedTransactionCountOfTotal 9 9
            .&&. walletFundsChange (walletAddress w1) (Value.adaValueOf (-100) <> Value.singleton currC tnC (-1))
            .&&. walletFundsChange (walletAddress w2) (Value.adaValueOf 30)
            .&&. walletFundsChange (walletAddress w3) (Value.adaValueOf 10)
            -- .&&. walletFundsChange (walletAddress w3) mempty
        )
        $ do
          act $ Start 1 (Ada.adaValueOf 100) tt
          act $ Propose 2 (Ada.adaValueOf 10) 3 12345
          act $ Add 4
          act $ Add 5
          act $ Pay 3
          act $ Propose 3 (Ada.adaValueOf 30) 2 12345
          act $ Add 5
          act $ Add 4
          act $ Pay 2
	, testProperty "QuickCheck ContractModel" $ QC.withMaxSuccess 100 prop_MultiSig
	, testProperty "QuickCheck CancelDL" (QC.expectFailure prop_Check)-}
    ]





checkPropMultiSigWithCoverage :: IO ()
checkPropMultiSigWithCoverage = do
  cr <-
    E.quickCheckWithCoverage QC.stdArgs options $ QC.withMaxSuccess 100 . E.propRunActionsWithOptions
  writeCoverageReport "MultiSig" cr


{-



{-
curSlot <- viewModelState currentSlot
      let deadline = toSlotNo . TimeSlot.posixTimeToEnclosingSlot lottoSlotConfig
                     $ TimeSlot.nominalDiffTimeToPOSIXTime (duration lottoSetup)-}




  
{-
instance RunModel MultiSigModel E.EmulatorM where
  perform _ cmd _ = lift $ voidCatch $ act cmd-}

voidCatch m = catchError (void m) (\ _ -> pure ())





-}

{-
import Control.Lens (At (at), makeLenses, to, (%=), (.=), (^.))
import Control.Monad (void, when)
import Control.Monad.Trans (lift)
import Data.Default (Default (def))
import Data.Foldable (Foldable (fold, length, null), sequence_)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust)
import GHC.Generics (Generic)

import Cardano.Api.Shelley (toPlutusData)
import Cardano.Node.Emulator qualified as E
import Cardano.Node.Emulator.Internal.Node.Params qualified as Params
import Cardano.Node.Emulator.Internal.Node.TimeSlot qualified as TimeSlot
import Cardano.Node.Emulator.Test (
  checkPredicateOptions,
  hasValidatedTransactionCountOfTotal,
  walletFundsChange,
  (.&&.),
 )
import Cardano.Node.Emulator.Test.Coverage (writeCoverageReport)
import Cardano.Node.Emulator.Test.NoLockedFunds (
  NoLockedFundsProof (nlfpMainStrategy, nlfpWalletStrategy),
  checkNoLockedFundsProofWithOptions,
  defaultNLFP,
 )
import Ledger (Slot, minAdaTxOutEstimated, POSIXTime)
import Ledger qualified
import Ledger.Tx.CardanoAPI (fromCardanoSlotNo)
import Ledger.Typed.Scripts qualified as Scripts
import Ledger.Value.CardanoAPI qualified as Value
import Plutus.Script.Utils.Ada qualified as Ada
import Plutus.Script.Utils.Value (Value, geq, AssetClass, CurrencySymbol, TokenName, assetClass, assetClassValue, valueOf)
import PlutusLedgerApi.V1.Time (POSIXTime)

import Plutus.Examples.MultiSig hiding (Input(..), Label(..))
import Plutus.Examples.MultiSigAPI (
  --Params (..),
  propose,
  add,
  pay,
  cancel,
  start,
  --typedValidator,
 )
import Plutus.Examples.MultiSig qualified as Impl
import PlutusTx (fromData, Data)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Monoid (inv)

import Cardano.Api (
  AddressInEra (AddressInEra),
  AllegraEraOnwards (AllegraEraOnwardsConway),
  IsShelleyBasedEra (shelleyBasedEra),
  TxOut (TxOut),
  TxValidityLowerBound (TxValidityLowerBound, TxValidityNoLowerBound),
  TxValidityUpperBound (TxValidityUpperBound),
  UTxO (unUTxO),
  toAddressAny,
  PolicyId (..),
  AssetName (..)
 )
--import Cardano.Api.Script
import Test.QuickCheck qualified as QC hiding ((.&&.))
import Test.QuickCheck.ContractModel (
  Action,
  Actions,
  ContractModel,
  DL,
  RunModel,
  action,
  anyActions_,
  assertModel,
  contractState,
  currentSlot,
  deposit,
  forAllDL,
  lockedValue,
  observe,
  symIsZero,
  utxo,
  viewContractState,
  viewModelState,
  wait,
  waitUntilDL,
  withdraw,
 )
import Test.QuickCheck.ContractModel qualified as QCCM
import Test.QuickCheck.ContractModel.ThreatModel (
  IsInputOrOutput (addressOf),
  ThreatModel,
  anyInputSuchThat,
  changeValidityRange,
  getRedeemer,
  shouldNotValidate,
 )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (
  Property,
  choose,
  chooseInteger,
  frequency,
  testProperty,
 )

import Control.Monad.Except (catchError)

--import Plutus.Contract.Test.Certification
--import Plutus.Contract.Test.Certification.Run
import Test.QuickCheck.DynamicLogic qualified as QCD

-}

{-
curr :: CurrencySymbol
curr = "c7c9864fcc779b5573d97e3beefe5dd3705bbfe41972acd9bb6ebe9e" 

tn :: TokenName
tn = "ThreadToken"

tt :: AssetClass
tt = assetClass curr tn

type Wallet = Integer

w1, w2, w3, w4, w5 :: Wallet
w1 = 1
w2 = 2
w3 = 3
w4 = 4
w5 = 5

walletAddress :: Wallet -> Ledger.CardanoAddress
walletAddress = (E.knownAddresses !!) . pred . fromIntegral

walletPrivateKey :: Wallet -> Ledger.PaymentPrivateKey
walletPrivateKey = (E.knownPaymentPrivateKeys !!) . pred . fromIntegral

testWallets :: [Wallet]
testWallets = [w1, w2, w3, w4, w5] -- removed five to increase collisions (, w6, w7, w8, w9, w10])

walletPaymentPubKeyHash :: Wallet -> Ledger.PaymentPubKeyHash
walletPaymentPubKeyHash =
  Ledger.PaymentPubKeyHash
    . Ledger.pubKeyHash
    . Ledger.unPaymentPubKey
    . (E.knownPaymentPublicKeys !!)
    . pred
    . fromIntegral

-}