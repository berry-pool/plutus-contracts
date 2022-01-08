import           Control.Monad        (void)
import           Ledger               (Address, ScriptContext(..), TxInfo(..))
import qualified Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Value         (Value, flattenValue,currencyMPSHash,singleton)
import           Ledger.Value         as Value
import           Ledger               hiding (Mint, mint)
import qualified Ledger.Address
import           Playground.Contract
import qualified Plutus.Contract
import qualified PlutusTx             as PlutusTx
import           PlutusTx.Prelude     hiding (Applicative (..),Semigroup(..))
import qualified PlutusTx.Prelude     as P
import qualified Prelude              as Haskell
import  Prelude              (Semigroup(..))
import qualified Data.ByteString.Char8 as C
import           Data.Map             as Map
import qualified Ledger.Ada            as Ada
import           Data.Void              (Void)
import           Plutus.Contract        as Contract
import           Plutus.V1.Ledger.Address
import           Ledger.Constraints.TxConstraints
import           Ledger.Tx
import           Plutus.ChainIndex.Tx
import           Control.Lens

data ValidatorData = ValidatorData {vdOwner :: !PaymentPubKeyHash, vdMaxSupply :: !Integer, vdThreadSymbol :: !CurrencySymbol}

data TokenData = TokenData {tdName :: !BuiltinByteString, tdValidatorHash :: !ValidatorHash, tdThreadSymbol :: !CurrencySymbol}

data ThreadData = ThreadData {thName :: !TokenName, thOref :: !TxOutRef}

data Action = Mint | Burn


-- the policy script that actually represents the NFT policy
mkTokenPolicy :: TokenData -> Action -> ScriptContext -> Bool
mkTokenPolicy tokenData action ctx = case action of
    Main.Mint -> checkMint
    Burn -> checkBurn
    where
        checkMint :: Bool
        checkMint = check flattenMint count
            where
                check [] _ = True
                check ((cs,tn,am):t) n = ownCurrencySymbol ctx == cs && tn == TokenName (tdName tokenData P.<> integerToByteString n) && am == 1 && check t (n+1)

        checkBurn :: Bool
        checkBurn = all (\(cs,_,am) -> cs == ownCurrencySymbol ctx && am == -1) (flattenValue (txInfoMint txInfo))

        txInfo :: TxInfo
        txInfo = scriptContextTxInfo ctx

        flattenMint :: [(CurrencySymbol, TokenName, Integer)]
        flattenMint = flattenValue (txInfoMint txInfo)

        count :: Integer
        count = let [(h, v)] = scriptOutputsAt (tdValidatorHash tokenData) txInfo in
            case findDatum h txInfo of
                Just (Datum d) -> case PlutusTx.fromBuiltinData d of
                        Just c -> case let [(cs,_,am)] = flattenValue v in cs == tdThreadSymbol tokenData && am == 1 of -- expects script output to contain thread token
                            True ->  c - length flattenMint -- needs to be subtraced, since this c is the value of the next count

        integerToByteString :: Integer -> BuiltinByteString
        integerToByteString n
            | n == 0 = "0"
            | n == 1 = "1"
            | n == 2 = "2"
            | n == 3 = "3"
            | n == 4 = "4"
            | n == 5 = "5"
            | n == 6 = "6"
            | n == 7 = "7"
            | n == 8 = "8"
            | n == 9 = "9"
            | otherwise = integerToByteString (n `P.divide` 10) P.<> integerToByteString (n `P.modulo` 10)

-- the policy that mints a single token in order to initialize the state machine of the validator (thread token)
mkThreadPolicy :: ThreadData -> Action -> ScriptContext -> Bool
mkThreadPolicy threadData action ctx = case action of
    Main.Mint -> hasUtxo && checkMint 1
    Burn -> checkMint (-1)
  where
    txInfo :: TxInfo
    txInfo = scriptContextTxInfo ctx

    hasUtxo :: Bool
    hasUtxo = any (\i -> txInInfoOutRef i == (thOref threadData)) $ txInfoInputs txInfo

    checkMint :: Integer -> Bool
    checkMint amt = case flattenValue (txInfoMint txInfo) of
        [(cs, tn, amt')] -> cs  == ownCurrencySymbol ctx && tn == thName threadData && amt' == amt
        _                -> False

-- the validator script that keeps track of the NFT supply and increments the mint id
mkTokenValidator :: ValidatorData -> Integer -> Action -> ScriptContext -> Bool
mkTokenValidator validatorData count action ctx =  Ledger.Constraints.TxConstraints.isSatisfiable (Constraints.mustBeSignedBy (vdOwner validatorData)) && case action of
    Main.Mint -> checkSupply && checkOutput
    Burn -> checkBurn
    where
        checkSupply :: Bool
        checkSupply = count < vdMaxSupply validatorData || vdMaxSupply validatorData == -1

        checkOutput :: Bool
        checkOutput = let [(cs,_,am)] = flattenValue outValue in cs == vdThreadSymbol validatorData && am == 1 && nextCount == count + length flattenMint

        checkBurn :: Bool
        checkBurn = let [(cs,_,am)] = flattenMint in cs == vdThreadSymbol validatorData && am == -1

        flattenMint :: [(CurrencySymbol, TokenName, Integer)]
        flattenMint = flattenValue (txInfoMint txInfo)

        txInfo :: TxInfo
        txInfo = scriptContextTxInfo ctx

        outValue :: Value
        nextCount :: Integer
        (outValue, nextCount) = case getContinuingOutputs ctx of
            [o] -> case txOutDatum o of
                Just h -> case findDatum h txInfo of
                   Just (Datum d) -> case PlutusTx.fromBuiltinData d of
                        Just c -> (txOutValue o, c)


threadPolicy :: ThreadData -> Scripts.MintingPolicy
threadPolicy threadData = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| wrap ||]) `PlutusTx.applyCode` PlutusTx.liftCode threadData
    where
        wrap threadData = Scripts.wrapMintingPolicy $ mkThreadPolicy threadData

tokenPolicy :: TokenData -> Scripts.MintingPolicy
tokenPolicy tokenData = mkMintingPolicyScript $
    $$(PlutusTx.compile [|| wrap ||]) `PlutusTx.applyCode` PlutusTx.liftCode tokenData
    where
        wrap tokenData = Scripts.wrapMintingPolicy $ mkTokenPolicy tokenData

threadSymbol :: ThreadData -> CurrencySymbol
threadSymbol threadData = scriptCurrencySymbol $ threadPolicy threadData

tokenSymbol :: TokenData -> CurrencySymbol
tokenSymbol tokenData = scriptCurrencySymbol $ tokenPolicy tokenData


tokenValidatorAddress :: ValidatorData -> Address
tokenValidatorAddress validatorData = Scripts.validatorAddress (tokenValidatorInstance validatorData)

data TokenValidator
instance Scripts.ValidatorTypes TokenValidator where
    type instance RedeemerType TokenValidator = Action
    type instance DatumType TokenValidator = Integer

tokenValidatorInstance :: ValidatorData -> Scripts.TypedValidator TokenValidator
tokenValidatorInstance validatorData = Scripts.mkTypedValidator @TokenValidator
    ($$(PlutusTx.compile [|| mkTokenValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode validatorData)
    $$(PlutusTx.compile [|| wrap ||])
     where
        wrap = Scripts.wrapValidator @Integer @Action


type MintSchema = Endpoint "simulate" MintParams

data MintParams = MintParams
    { mpMaxSupply  :: Integer
    , mpName     :: TokenName
    }
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (FromJSON, ToJSON, ToSchema)


-- this endpoint simulate the minting and burning process of an NFT series. It's not meant as a real contract endpoint
-- real off-chain endpoints have to be implemented and are not part of this file
simulate :: AsContractError e => Promise () MintSchema e ()
simulate = endpoint @"simulate" @MintParams $ \(MintParams{..}) -> do

     -- init contract with thread token
    pk    <- ownPaymentPubKeyHash
    utxos <- utxosAt (Ledger.pubKeyHashAddress pk Nothing)
    let pkh = pk
        (oref : _) =  Map.keys utxos
        threadData = ThreadData {thName = "Mint", thOref = oref}
        cs = threadSymbol threadData
        threadValue = Value.singleton cs (thName threadData) 1
        vh = Scripts.validatorHash (tokenValidatorInstance validatorData)

        validatorData = ValidatorData {vdOwner = pkh, vdMaxSupply = mpMaxSupply, vdThreadSymbol = cs}
        tokenData = TokenData {tdName = unTokenName mpName, tdValidatorHash = vh, tdThreadSymbol = cs}

        lookups = Constraints.mintingPolicy (threadPolicy threadData) <>
                Constraints.unspentOutputs utxos
        tx = Constraints.mustSpendPubKeyOutput oref <> Constraints.mustMintValueWithRedeemer (Redeemer (PlutusTx.toBuiltinData Main.Mint)) threadValue <>
            Constraints.mustPayToOtherScript vh (Datum (PlutusTx.toBuiltinData (0 :: Integer))) threadValue
    void $ submitTxConstraintsWith @TokenValidator lookups tx

    -- wait 1 slot
    slot <- currentSlot
    _ <- awaitSlot (slot+1)


    -- mint NFT with id 0
    simpleutxos <- utxosAt(tokenValidatorAddress validatorData)
    utxos <- utxosTxOutTxAt (tokenValidatorAddress validatorData)
    let count = let [(_,o)] = Map.toList utxos in getCount o
        tn = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show count)))
        cs = scriptCurrencySymbol $ tokenPolicy tokenData
        value = Value.singleton cs tn 1
        lookups = Constraints.typedValidatorLookups (tokenValidatorInstance validatorData) <>
                Constraints.mintingPolicy (tokenPolicy tokenData) <>
                Constraints.unspentOutputs simpleutxos
        tx = collectFromScript simpleutxos Main.Mint <>
            Constraints.mustMintValue value <>
            Constraints.mustPayToTheScript (count+1) threadValue
    void $ submitTxConstraintsWith @TokenValidator lookups tx


    -- wait 1 slot
    slot <- currentSlot
    _ <- awaitSlot (slot+1)

    -- mint NFT with id 1
    simpleutxos <- utxosAt(tokenValidatorAddress validatorData)
    utxos <- utxosTxOutTxAt (tokenValidatorAddress validatorData)
    let count = let [(_,o)] = Map.toList utxos in getCount o
        tn = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show count)))
        cs = scriptCurrencySymbol $ tokenPolicy tokenData
        value = Value.singleton cs tn 1
        lookups = Constraints.typedValidatorLookups (tokenValidatorInstance validatorData) <>
                Constraints.mintingPolicy (tokenPolicy tokenData) <>
                Constraints.unspentOutputs simpleutxos
        tx = collectFromScript simpleutxos Main.Mint <>
            Constraints.mustMintValue value <>
            Constraints.mustPayToTheScript (count+1) threadValue
    void $ submitTxConstraintsWith @TokenValidator lookups tx

    -- wait 1 slot
    slot <- currentSlot
    _ <- awaitSlot (slot+1)

    -- batch mint NFT with id 2, id 3
    simpleutxos <- utxosAt(tokenValidatorAddress validatorData)
    utxos <- utxosTxOutTxAt (tokenValidatorAddress validatorData)
    let count = let [(_,o)] = Map.toList utxos in getCount o
        tn0 = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show count)))
        tn1 = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show (count+1))))
        cs = scriptCurrencySymbol $ tokenPolicy tokenData
        value = Value.singleton cs tn0 1 <> Value.singleton cs tn1 1
        lookups = Constraints.typedValidatorLookups (tokenValidatorInstance validatorData) <>
                Constraints.mintingPolicy (tokenPolicy tokenData) <>
                Constraints.unspentOutputs simpleutxos
        tx = collectFromScript simpleutxos Main.Mint <>
            Constraints.mustMintValue value <>
            Constraints.mustPayToTheScript (count+2) threadValue
    void $ submitTxConstraintsWith @TokenValidator lookups tx

    -- mint next id 4, id 5, and so on...

    -- wait 1 slot
    slot <- currentSlot
    _ <- awaitSlot (slot+1)

    -- burn thread token
    utxos <- utxosAt (tokenValidatorAddress validatorData)
    let cs = threadSymbol threadData
        threadValue = Value.singleton cs (thName threadData) (-1)
        lookups = Constraints.mintingPolicy (threadPolicy threadData) <>
                Constraints.typedValidatorLookups (tokenValidatorInstance validatorData) <>
                Constraints.unspentOutputs utxos
        tx = collectFromScript utxos Burn <> Constraints.mustMintValueWithRedeemer (Redeemer (PlutusTx.toBuiltinData Burn)) threadValue
    void $ submitTxConstraintsWith @TokenValidator lookups tx

    -- wait 1 slot
    slot <- currentSlot
    _ <- awaitSlot (slot+1)

    -- burn freshly minted NFTs as example
    utxos <- utxosAt (Ledger.pubKeyHashAddress pk Nothing)
    let cs = scriptCurrencySymbol $ tokenPolicy tokenData
        tn0 = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show 0)))
        tn1 = TokenName (unTokenName mpName <> toBuiltin (C.pack (Haskell.show 1)))
        value = Value.singleton cs tn0 (-1) <> Value.singleton cs tn1 (-1)
        lookups = Constraints.mintingPolicy (tokenPolicy tokenData) <>
                Constraints.unspentOutputs utxos
        tx = Constraints.mustMintValueWithRedeemer (Redeemer (PlutusTx.toBuiltinData Burn)) value
    void $ submitTxConstraintsWith @TokenValidator lookups tx


-- helper function
getCount :: (ChainIndexTxOut, ChainIndexTx) -> Integer
getCount (o,u) = case txOutDatum (Ledger.Tx.toTxOut o) of
    Just h -> do
        let [(_,datum)] = Haskell.filter (\(h',_) -> h == h') (Map.toList (_citxData u))
        let parsedDatum = PlutusTx.fromBuiltinData (getDatum datum) :: Maybe Integer
        case parsedDatum of
            Just b -> b
            _ -> traceError "expected datum"
    _ -> traceError "expected datum"

PlutusTx.makeLift ''ValidatorData
PlutusTx.makeIsDataIndexed ''ValidatorData [('ValidatorData,0)]

PlutusTx.makeLift ''TokenData
PlutusTx.makeIsDataIndexed ''TokenData [('TokenData,0)]

PlutusTx.makeLift ''ThreadData
PlutusTx.makeIsDataIndexed ''ThreadData [('ThreadData,0)]

PlutusTx.makeLift ''Action
PlutusTx.makeIsDataIndexed ''Action [('Main.Mint,0),('Burn,1)]


contract :: AsContractError e => Contract () MintSchema e ()
contract = selectList [simulate]

endpoints :: AsContractError e => Contract () MintSchema e ()
endpoints = contract

mkSchemaDefinitions ''MintSchema

$(mkKnownCurrencies [])