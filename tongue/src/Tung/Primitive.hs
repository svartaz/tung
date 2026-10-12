{-# LANGUAGE GADTs #-}

-- | shared host ABI catalogues for the checker/runtime boundary.
module Tung.Primitive
  ( HostBinding (..),
    HostSignature (..),
    HostType (..),
    HostDataSchema (..),
    hostBindings,
    hostDataSchemas,
    hostArity,
    primitiveTypeNames,
    opaqueTypeFamilyNames,
    hostTypeId,
    onlyConstructorId,
    yeaConstructorId,
    nayConstructorId,
    emptyConstructorId,
    consConstructorId,
    noneConstructorId,
    someConstructorId,
    productConstructorId,
    processResultConstructorId,
    requestConstructorId,
    responseConstructorId,
    tableConstructorId,
    leftConstructorId,
    rightConstructorId,
    findForeignBinding,
    HostValue (..),
    pureOperation,
    naturalZeroId,
    naturalSuccessorId,
    integerPositiveId,
    integerNegativeId,
    listName,
    oneName,
    requestName,
  )
where

import Data.Char (ord)
import Data.List (find)
import GHC.TypeLits (Natural)
import Text.Read (readMaybe)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Name (importNamespace)
import Tung.Token (unicodeScalar)

-- host types are first order, except that an argument may be a function.
data HostType
  = HostVar String
  | HostCon String
  | HostApp String [HostType]
  | HostArrow [HostType] HostType
  deriving (Eq, Show)

data HostSignature = HostSignature
  { hostVariables :: [String],
    hostArguments :: [HostType],
    hostResult :: HostType
  }
  deriving (Eq, Show)

-- every host operation is reached through an annotated `fremmed` let.
data HostBinding = HostBinding
  { hostName :: String,
    hostSignature :: HostSignature
  }
  deriving (Eq, Show)

-- a host data type is the `ilk` of this name declared in this bookhoard file;
-- the runtime readeth its constructors by identity.
data HostData = HostData
  { hostDataSource :: FilePath,
    hostDataName :: String
  }

-- nominal data declarations used by host operations have a fixed constructor
-- ABI. signatures reuse the same type language as the operation catalogue.
data HostDataSchema = HostDataSchema
  { hostDataType :: String,
    hostDataParameters :: [String],
    hostDataConstructors :: [(SymbolId, HostSignature)]
  }
  deriving (Eq, Show)

oneData, twoData, listData, optionData, productData, sumData, tableData :: HostData
oneData = HostData "ilk/one.tung" "𝟙"
twoData = HostData "ilk/two.tung" "𝟚"
listData = HostData "ilk/list.tung" "list"
optionData = HostData "ilk/maybe.tung" "maybe"
productData = HostData "ilk/product.tung" "∏"
-- a fallible host deed returneth `string ∑ α`: an error message or a result.
sumData = HostData "ilk/sum.tung" "∑"
tableData = HostData "ilk/wordbook.tung" "wordbook"

processResultData, requestData, responseData :: HostData
processResultData = HostData "process/result.tung" "_process_result"
requestData = HostData "web/request.tung" "_request"
responseData = HostData "web/response.tung" "_response"

hostData :: [HostData]
hostData =
  [ oneData,
    twoData,
    listData,
    optionData,
    productData,
    sumData,
    tableData,
    processResultData,
    requestData,
    responseData
  ]

hostDataSchemas :: [HostDataSchema]
hostDataSchemas =
  [ schema oneData [] [("only", [])],
    schema twoData [] [("yea", []), ("nay", [])],
    schema optionData ["a"] [("none", []), ("some", [a])],
    schema listData ["a"] [("empty", []), ("‥", [a, app listData [a]])],
    schema productData ["a", "b"] [("both", [a, b])],
    schema sumData ["a", "b"] [("incast₀", [a]), ("incast₁", [b])],
    schema tableData ["a", "b"] [("from_list", [app listData [app productData [a, b]]])],
    schema processResultData [] [("process_result", [HostCon "ℤ", text, text])],
    schema requestData [] [("request", [text, text, headers, text])],
    schema responseData [] [("response", [HostCon "ℕ", headers, text])]
  ]
  where
    a = HostVar "a"
    b = HostVar "b"
    text = HostCon "string"
    headers = app tableData [text, text]
    app dataType = HostApp (canonicalDataTypeName dataType)
    schema dataType variables constructors =
      let name = canonicalDataTypeName dataType
          result = if null variables then HostCon name else HostApp name (map HostVar variables)
       in HostDataSchema name variables [(constructorId dataType constructor, HostSignature variables fields result) | (constructor, fields) <- constructors]

-- native types and type operators are available before library loading.
-- opaque unary families have no constructors or eliminators. their values
-- carry runtime resources, so an ordinary data schema cannot represent them.
opaqueTypeFamilyNames :: [String]
opaqueTypeFamilyNames = ["deed", "task"]

primitiveTypeNames :: [String]
primitiveTypeNames = ["ℕ", "ℤ", "float", "unicode", "string"] ++ opaqueTypeFamilyNames

hostTypeId :: String -> Maybe SymbolId
hostTypeId name = dataTypeId <$> find matches hostData
  where
    matches dataType = name == hostDataName dataType || name == canonicalDataTypeName dataType

-- `ℕ` is primitive but structural: `0` and `n heir` are its
-- constructors, and a literal is a compact chain of them.
naturalZeroId, naturalSuccessorId :: SymbolId
naturalZeroId = SymbolId PrimitiveModule "0"
naturalSuccessorId = SymbolId PrimitiveModule "heir"

-- `ℤ` is structural in the same way: `n overnaught` is `n` and
-- `n heir_undernaught` is `-(n + 1)`, so each integer hath one form.
integerPositiveId, integerNegativeId :: SymbolId
integerPositiveId = SymbolId PrimitiveModule "overnaught"
integerNegativeId = SymbolId PrimitiveModule "heir_undernaught"

onlyConstructorId, yeaConstructorId, nayConstructorId :: SymbolId
onlyConstructorId = constructorId oneData "only"
yeaConstructorId = constructorId twoData "yea"
nayConstructorId = constructorId twoData "nay"

emptyConstructorId, consConstructorId :: SymbolId
emptyConstructorId = constructorId listData "empty"
consConstructorId = constructorId listData "‥"

noneConstructorId, someConstructorId :: SymbolId
noneConstructorId = constructorId optionData "none"
someConstructorId = constructorId optionData "some"

productConstructorId :: SymbolId
productConstructorId = constructorId productData "both"

leftConstructorId, rightConstructorId :: SymbolId
leftConstructorId = constructorId sumData "incast₀"
rightConstructorId = constructorId sumData "incast₁"

processResultConstructorId, requestConstructorId, responseConstructorId, tableConstructorId :: SymbolId
processResultConstructorId = constructorId processResultData "process_result"
requestConstructorId = constructorId requestData "request"
responseConstructorId = constructorId responseData "response"
tableConstructorId = constructorId tableData "from_list"

-- catalogue names of the host data types.
listName, optionName, productName, oneName, twoName :: String
listName = canonicalDataTypeName listData
optionName = canonicalDataTypeName optionData
productName = canonicalDataTypeName productData
oneName = canonicalDataTypeName oneData
twoName = canonicalDataTypeName twoData

requestName :: String
requestName = canonicalDataTypeName requestData

canonicalDataTypeName :: HostData -> String
canonicalDataTypeName HostData {hostDataSource, hostDataName} = importNamespace hostDataSource ++ "~" ++ hostDataName

constructorId :: HostData -> String -> SymbolId
constructorId HostData {hostDataSource, hostDataName} name = SymbolId (SourceModule hostDataSource) (hostDataName ++ "@" ++ name)

dataTypeId :: HostData -> SymbolId
dataTypeId HostData {hostDataSource, hostDataName} = SymbolId (SourceModule hostDataSource) hostDataName

hostArity :: HostBinding -> Int
hostArity = length . hostArguments . hostSignature

findForeignBinding :: String -> Maybe HostBinding
findForeignBinding key = find ((== key) . hostName) hostBindings

hostBindings :: [HostBinding]
hostBindings =
  map fst pureBindings
    ++ [
         -- deeds: actions that only the runner performeth.
         deed "deed_sheer" ["a"] [variable "a"] (action (variable "a")),
         deed "deed_bind" ["a", "b"] [action (variable "a"), HostArrow [variable "a"] (action (variable "b"))] (action (variable "b")),
         -- the restricted fixed point: a deed may repeat itself, a pure value may not.
         deed "deed_steadfast" ["a"] [HostArrow [action (variable "a")] (action (variable "a"))] (action (variable "a")),
         deed "write" [] [text] (action one),
         deed "read" [] [] (action (option text)),
         deed "random" [] [] (action float),
         deed "unix_time" [] [] (action integer),
         deed "sleep" [] [natural] (action one),
         deed "fork" ["a"] [action (variable "a")] (action (task (variable "a"))),
         deed "wait" ["a"] [task (variable "a")] (action (option (variable "a"))),
         deed "wait_for" ["a"] [task (variable "a"), natural] (action (option (variable "a"))),
         deed "outstrike" ["a"] [task (variable "a")] (action one),
         deed "read_file" [] [text] (action (outcome text)),
         deed "write_file" [] [text, text] (action (outcome one)),
         deed "athang_file" [] [text, text] (action (outcome one)),
         deed "arguments" [] [] (action (list text)),
         deed "environment" [] [text] (action (option text)),
         deed "exit" ["a"] [natural] (action (variable "a")),
         deed "run_process" [] [text, list text] (action (outcome (HostCon (canonicalDataTypeName processResultData)))),
         deed "serve" [] [natural, HostArrow [HostCon (canonicalDataTypeName requestData)] (action (HostCon (canonicalDataTypeName responseData)))] (action text)
       ]
  where
    natural = HostCon "ℕ"
    integer = HostCon "ℤ"
    float = HostCon "float"
    text = HostCon "string"
    one = HostCon (canonicalDataTypeName oneData)
    variable = HostVar
    action value = HostApp "deed" [value]
    task value = HostApp "task" [value]
    outcome value = HostApp (canonicalDataTypeName sumData) [text, value]
    deed name variables arguments result = HostBinding name (HostSignature variables arguments result)
    list value = HostApp (canonicalDataTypeName listData) [value]
    option value = HostApp (canonicalDataTypeName optionData) [value]

-- a value crosseth the host boundary in this shape. each runtime convertth its
-- own representation, so pure operations have one meaning everywhere.
data HostValue
  = HostNatural Natural
  | HostInteger Integer
  | HostFloat Double
  | HostUnicode Char
  | HostText String
  | HostTruth Bool
  | HostOption (Maybe HostValue)
  | HostPair HostValue HostValue
  | HostList [HostValue]
  deriving (Eq, Show)

-- the total pure operations of the catalogue. a partial result is an option:
-- division by zero, a negative natural, a non-scalar code point, an infinite
-- floor, or unreadable text yieldeth none. integer division is euclidean.
pureOperation :: String -> Maybe ([HostValue] -> Maybe HostValue)
pureOperation key = snd <$> find ((== key) . hostName . fst) pureBindings

-- codecs are private trusted ABI mappings. the binding GADT coupleth each
-- native function to its input and result codecs; one entry deriveth both
-- the checker signature and the adapter used by normalisation and execution.
data Codec a = Codec
  { codecType :: HostType,
    encodeHost :: a -> HostValue,
    decodeHost :: HostValue -> Maybe a
  }

data PureBinding where
  UnaryBinding :: String -> Codec a -> Codec b -> (a -> b) -> PureBinding
  BinaryBinding :: String -> Codec a -> Codec b -> Codec c -> (a -> b -> c) -> PureBinding

eraseBinding :: PureBinding -> (HostBinding, [HostValue] -> Maybe HostValue)
eraseBinding = \case
  UnaryBinding name argument result function ->
    ( HostBinding name (HostSignature [] [codecType argument] (codecType result)),
      \case [value] -> encodeHost result . function <$> decodeHost argument value; _ -> Nothing
    )
  BinaryBinding name left right result function ->
    ( HostBinding name (HostSignature [] [codecType left, codecType right] (codecType result)),
      \case [a, b] -> encodeHost result <$> (function <$> decodeHost left a <*> decodeHost right b); _ -> Nothing
    )

natural :: Codec Natural
natural = Codec (HostCon "ℕ") HostNatural \case HostNatural value -> Just value; _ -> Nothing

integer :: Codec Integer
integer = Codec (HostCon "ℤ") HostInteger \case HostInteger value -> Just value; _ -> Nothing

float :: Codec Double
float = Codec (HostCon "float") HostFloat \case HostFloat value -> Just value; _ -> Nothing

unicode :: Codec Char
unicode = Codec (HostCon "unicode") HostUnicode \case HostUnicode value -> Just value; _ -> Nothing

text :: Codec String
text = Codec (HostCon "string") HostText \case HostText value -> Just value; _ -> Nothing

truth :: Codec Bool
truth = Codec (HostCon twoName) HostTruth \case HostTruth value -> Just value; _ -> Nothing

optionCodec :: Codec a -> Codec (Maybe a)
optionCodec inner = Codec (HostApp optionName [codecType inner]) (HostOption . fmap (encodeHost inner)) \case
  HostOption value -> traverse (decodeHost inner) value
  _ -> Nothing

-- producing the pair constructor needeth neither numeric payload yet.
pairCodec :: Codec a -> Codec b -> Codec (a, b)
pairCodec left right = Codec (HostApp productName [codecType left, codecType right]) (\ ~(a, b) -> HostPair (encodeHost left a) (encodeHost right b)) \case
  HostPair a b -> (,) <$> decodeHost left a <*> decodeHost right b
  _ -> Nothing

listCodec :: Codec a -> Codec [a]
listCodec inner = Codec (HostApp listName [codecType inner]) (HostList . map (encodeHost inner)) \case
  HostList values -> traverse (decodeHost inner) values
  _ -> Nothing

pureBindings :: [(HostBinding, [HostValue] -> Maybe HostValue)]
pureBindings =
  map
    eraseBinding
    [ UnaryBinding "natural_to_wholetale" natural integer toInteger,
      UnaryBinding "wholetale_to_natural" integer (optionCodec natural) \a -> if a >= 0 then Just (fromInteger a) else Nothing,
      BinaryBinding "eke_wholetale" integer integer integer (+),
      BinaryBinding "offdraw_wholetale" integer integer integer (-),
      BinaryBinding "offdraw_natural" natural natural natural \a b -> if b > a then 0 else a - b,
      BinaryBinding "fold_wholetale" integer integer integer (*),
      BinaryBinding "deal_leftover_wholetale" integer integer (optionCodec (pairCodec integer integer)) \a b -> if b == 0 then Nothing else Just (euclidean a b),
      BinaryBinding "eke_float" float float float (+),
      BinaryBinding "offdraw_float" float float float (-),
      BinaryBinding "fold_float" float float float (*),
      BinaryBinding "deal_float" float float float (/),
      UnaryBinding "sine_float" float float sin,
      -- the angle of the point (real, imaginary), in [0, 2π).
      BinaryBinding "arctan_float" float float float \real imaginary -> let angle = atan2 imaginary real in if angle < 0 then angle + 2 * pi else angle,
      UnaryBinding "exponent_float" float float exp,
      UnaryBinding "logarithm_float" float float log,
      UnaryBinding "⌊" float (optionCodec integer) \a -> if isNaN a || isInfinite a then Nothing else Just (floor a),
      BinaryBinding "same_wholetale" integer integer truth (==),
      UnaryBinding "wholetale_to_string" integer text show,
      UnaryBinding "float_to_string" float text show,
      UnaryBinding "unicode_to_natural" unicode natural (fromIntegral . ord),
      UnaryBinding "natural_to_unicode" natural (optionCodec unicode) (unicodeScalar . toInteger),
      UnaryBinding "behead_string" text (optionCodec (pairCodec unicode text)) \case first : rest -> Just (first, rest); [] -> Nothing,
      UnaryBinding "string_to_list" text (listCodec unicode) id,
      UnaryBinding "list_to_string" (listCodec unicode) text id,
      BinaryBinding "yoke_string" text text text (++),
      BinaryBinding "same_string" text text truth (==),
      BinaryBinding "same_unicode" unicode unicode truth (==),
      BinaryBinding "at_most_string" text text truth (<=),
      BinaryBinding "at_most_unicode" unicode unicode truth (<=),
      BinaryBinding "at_most_wholetale" integer integer truth (<=),
      BinaryBinding "same_float" float float truth (==),
      BinaryBinding "at_most_float" float float truth (<=),
      UnaryBinding "string_to_float" text (optionCodec float) readMaybe,
      BinaryBinding "same_natural" natural natural truth (==),
      BinaryBinding "at_most_natural" natural natural truth (<=),
      BinaryBinding "eke_natural" natural natural natural (+),
      BinaryBinding "fold_natural" natural natural natural (*),
      BinaryBinding "deal_leftover_natural" natural natural (optionCodec (pairCodec natural natural)) \a b -> if b == 0 then Nothing else Just (a `div` b, a `mod` b),
      UnaryBinding "natural_to_string" natural text show
    ]
  where
    -- the remainder is never negative.
    euclidean a b =
      let (quotient, remainder) = a `divMod` b
       in if remainder < 0 then (quotient + 1, remainder - b) else (quotient, remainder)
