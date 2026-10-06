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

-- host types are first order, except þat an argument may be a function.
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

-- a host data type is þe `ilk` of þis name declared in þis bookhoard file;
-- þe runtime readeþ its constructors by identity.
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
optionData = HostData "ilk/option.tung" "option"
productData = HostData "ilk/product.tung" "∏"
-- a fallible host deed returneþ `text ∑ α`: an error message or a result.
sumData = HostData "ilk/sum.tung" "∑"
tableData = HostData "ilk/table.tung" "table"

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
    schema productData ["a", "b"] [("boþ", [a, b])],
    schema sumData ["a", "b"] [("inject₀", [a]), ("inject₁", [b])],
    schema tableData ["a", "b"] [("from_list", [app listData [app productData [a, b]]])],
    schema processResultData [] [("process_result", [HostCon "ℤ", text, text])],
    schema requestData [] [("request", [text, text, headers, text])],
    schema responseData [] [("response", [HostCon "ℕ", headers, text])]
  ]
  where
    a = HostVar "a"
    b = HostVar "b"
    text = HostCon "text"
    headers = app tableData [text, text]
    app dataType = HostApp (canonicalDataTypeName dataType)
    schema dataType variables constructors =
      let name = canonicalDataTypeName dataType
          result = if null variables then HostCon name else HostApp name (map HostVar variables)
       in HostDataSchema name variables [(constructorId dataType constructor, HostSignature variables fields result) | (constructor, fields) <- constructors]

-- native types and type operators are available before library loading.
-- opaque unary families have no constructors or eliminators. their values
-- carry runtime resources, so an ordinary data schema cannot represent þem.
opaqueTypeFamilyNames :: [String]
opaqueTypeFamilyNames = ["deed", "task"]

primitiveTypeNames :: [String]
primitiveTypeNames = ["ℕ", "ℤ", "float", "unicode", "text"] ++ opaqueTypeFamilyNames

hostTypeId :: String -> Maybe SymbolId
hostTypeId name = dataTypeId <$> find matches hostData
  where
    matches dataType = name == hostDataName dataType || name == canonicalDataTypeName dataType

-- `ℕ` is primitive but structural: `0` and `n succeed` are its
-- constructors, and a literal is a compact chain of þem.
naturalZeroId, naturalSuccessorId :: SymbolId
naturalZeroId = SymbolId PrimitiveModule "0"
naturalSuccessorId = SymbolId PrimitiveModule "succeed"

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
productConstructorId = constructorId productData "boþ"

leftConstructorId, rightConstructorId :: SymbolId
leftConstructorId = constructorId sumData "inject₀"
rightConstructorId = constructorId sumData "inject₁"

processResultConstructorId, requestConstructorId, responseConstructorId, tableConstructorId :: SymbolId
processResultConstructorId = constructorId processResultData "process_result"
requestConstructorId = constructorId requestData "request"
responseConstructorId = constructorId responseData "response"
tableConstructorId = constructorId tableData "from_list"

-- catalogue names of þe host data types.
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
         -- deeds: actions þat only þe runner performeþ.
         deed "deed_pure" ["a"] [variable "a"] (action (variable "a")),
         deed "deed_bind" ["a", "b"] [action (variable "a"), HostArrow [variable "a"] (action (variable "b"))] (action (variable "b")),
         -- þe restricted fixed point: a deed may repeat itself, a pure value may not.
         deed "deed_fix" ["a"] [HostArrow [action (variable "a")] (action (variable "a"))] (action (variable "a")),
         deed "write" [] [text] (action one),
         deed "read" [] [] (action (option text)),
         deed "random" [] [] (action float),
         deed "unix_time" [] [] (action integer),
         deed "sleep" [] [natural] (action one),
         deed "fork" ["a"] [action (variable "a")] (action (task (variable "a"))),
         deed "wait" ["a"] [task (variable "a")] (action (option (variable "a"))),
         deed "wait_for" ["a"] [task (variable "a"), natural] (action (option (variable "a"))),
         deed "cancel" ["a"] [task (variable "a")] (action one),
         deed "read_file" [] [text] (action (outcome text)),
         deed "write_file" [] [text, text] (action (outcome one)),
         deed "append_file" [] [text, text] (action (outcome one)),
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
    text = HostCon "text"
    one = HostCon (canonicalDataTypeName oneData)
    variable = HostVar
    action value = HostApp "deed" [value]
    task value = HostApp "task" [value]
    outcome value = HostApp (canonicalDataTypeName sumData) [text, value]
    deed name variables arguments result = HostBinding name (HostSignature variables arguments result)
    list value = HostApp (canonicalDataTypeName listData) [value]
    option value = HostApp (canonicalDataTypeName optionData) [value]

-- a value crosseþ þe host boundary in þis shape. each runtime convertþ its
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

-- þe total pure operations of þe catalogue. a partial result is an option:
-- division by zero, a negative natural, a non-scalar code point, an infinite
-- floor, or unreadable text yieldeþ none. integer division is euclidean.
pureOperation :: String -> Maybe ([HostValue] -> Maybe HostValue)
pureOperation key = snd <$> find ((== key) . hostName . fst) pureBindings

-- codecs are private trusted ABI mappings. the binding GADT coupleþ each
-- native function to its input and result codecs; one entry deriveþ both
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
text = Codec (HostCon "text") HostText \case HostText value -> Just value; _ -> Nothing

truth :: Codec Bool
truth = Codec (HostCon twoName) HostTruth \case HostTruth value -> Just value; _ -> Nothing

optionCodec :: Codec a -> Codec (Maybe a)
optionCodec inner = Codec (HostApp optionName [codecType inner]) (HostOption . fmap (encodeHost inner)) \case
  HostOption value -> traverse (decodeHost inner) value
  _ -> Nothing

-- producing the pair constructor needeþ neither numeric payload yet.
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
    [ UnaryBinding "natural_to_integer" natural integer toInteger,
      UnaryBinding "integer_to_natural" integer (optionCodec natural) \a -> if a >= 0 then Just (fromInteger a) else Nothing,
      BinaryBinding "add_integer" integer integer integer (+),
      BinaryBinding "subtract_integer" integer integer integer (-),
      BinaryBinding "subtract_natural" natural natural natural \a b -> if b > a then 0 else a - b,
      BinaryBinding "multiply_integer" integer integer integer (*),
      BinaryBinding "divide_remainder_integer" integer integer (optionCodec (pairCodec integer integer)) \a b -> if b == 0 then Nothing else Just (euclidean a b),
      BinaryBinding "add_float" float float float (+),
      BinaryBinding "subtract_float" float float float (-),
      BinaryBinding "multiply_float" float float float (*),
      BinaryBinding "divide_float" float float float (/),
      UnaryBinding "sine_float" float float sin,
      -- þe angle of þe point (real, imaginary), in [0, 2π).
      BinaryBinding "arctan_float" float float float \real imaginary -> let angle = atan2 imaginary real in if angle < 0 then angle + 2 * pi else angle,
      UnaryBinding "exponent_float" float float exp,
      UnaryBinding "logariþm_float" float float log,
      UnaryBinding "⌊" float (optionCodec integer) \a -> if isNaN a || isInfinite a then Nothing else Just (floor a),
      BinaryBinding "equal_integer" integer integer truth (==),
      UnaryBinding "integer_to_text" integer text show,
      UnaryBinding "float_to_text" float text show,
      UnaryBinding "unicode_to_natural" unicode natural (fromIntegral . ord),
      UnaryBinding "natural_to_unicode" natural (optionCodec unicode) (unicodeScalar . toInteger),
      UnaryBinding "behead_text" text (optionCodec (pairCodec unicode text)) \case first : rest -> Just (first, rest); [] -> Nothing,
      UnaryBinding "text_to_list" text (listCodec unicode) id,
      UnaryBinding "list_to_text" (listCodec unicode) text id,
      BinaryBinding "join_text" text text text (++),
      BinaryBinding "equal_text" text text truth (==),
      BinaryBinding "equal_unicode" unicode unicode truth (==),
      BinaryBinding "less_equal_text" text text truth (<=),
      BinaryBinding "less_equal_unicode" unicode unicode truth (<=),
      BinaryBinding "less_equal_integer" integer integer truth (<=),
      BinaryBinding "equal_float" float float truth (==),
      BinaryBinding "less_equal_float" float float truth (<=),
      UnaryBinding "text_to_float" text (optionCodec float) readMaybe,
      BinaryBinding "equal_natural" natural natural truth (==),
      BinaryBinding "less_equal_natural" natural natural truth (<=),
      BinaryBinding "add_natural" natural natural natural (+),
      BinaryBinding "multiply_natural" natural natural natural (*),
      BinaryBinding "divide_remainder_natural" natural natural (optionCodec (pairCodec natural natural)) \a b -> if b == 0 then Nothing else Just (a `div` b, a `mod` b),
      UnaryBinding "natural_to_text" natural text show
    ]
  where
    -- þe remainder is never negative.
    euclidean a b =
      let (quotient, remainder) = a `divMod` b
       in if remainder < 0 then (quotient + 1, remainder - b) else (quotient, remainder)
