{-# LANGUAGE ViewPatterns #-}

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
    canonicalHostTypeName,
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
    optionName,
    productName,
    sumName,
    tableName,
    oneName,
    twoName,
    processResultName,
    requestName,
    responseName,
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

-- | find the canonical imported name of a host-provided data type.
canonicalHostTypeName :: String -> Maybe String
canonicalHostTypeName name = canonicalDataTypeName <$> find ((== name) . hostDataName) hostData

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
listName, optionName, productName, sumName, tableName, oneName, twoName :: String
listName = canonicalDataTypeName listData
optionName = canonicalDataTypeName optionData
productName = canonicalDataTypeName productData
sumName = canonicalDataTypeName sumData
tableName = canonicalDataTypeName tableData
oneName = canonicalDataTypeName oneData
twoName = canonicalDataTypeName twoData

processResultName, requestName, responseName :: String
processResultName = canonicalDataTypeName processResultData
requestName = canonicalDataTypeName requestData
responseName = canonicalDataTypeName responseData

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
  [ foreignBinding "natural_to_integer" (unary natural integer),
    foreignBinding "integer_to_natural" (unary integer (option natural)),
    foreignBinding "add_integer" (binary integer integer integer),
    foreignBinding "subtract_integer" (binary integer integer integer),
    foreignBinding "subtract_natural" (binary natural natural natural),
    foreignBinding "multiply_integer" (binary integer integer integer),
    foreignBinding "divide_remainder_integer" (binary integer integer (option (product integer integer))),
    foreignBinding "add_float" (binary float float float),
    foreignBinding "subtract_float" (binary float float float),
    foreignBinding "multiply_float" (binary float float float),
    foreignBinding "divide_float" (binary float float float),
    foreignBinding "sine_float" (unary float float),
    foreignBinding "arctan_float" (binary float float float),
    foreignBinding "exponent_float" (unary float float),
    foreignBinding "logariþm_float" (unary float float),
    foreignBinding "⌊" (unary float (option integer)),
    foreignBinding "equal_integer" (binary integer integer two),
    foreignBinding "integer_to_text" (unary integer text),
    foreignBinding "float_to_text" (unary float text),
    foreignBinding "unicode_to_natural" (unary unicode natural),
    foreignBinding "natural_to_unicode" (unary natural (option unicode)),
    foreignBinding "behead_text" (unary text (option (product unicode text))),
    foreignBinding "text_to_list" (unary text (list unicode)),
    foreignBinding "list_to_text" (unary (list unicode) text),
    foreignBinding "join_text" (binary text text text),
    foreignBinding "equal_text" (binary text text two),
    foreignBinding "equal_unicode" (binary unicode unicode two),
    foreignBinding "less_equal_text" (binary text text two),
    foreignBinding "less_equal_unicode" (binary unicode unicode two),
    foreignBinding "less_equal_integer" (binary integer integer two),
    foreignBinding "equal_float" (binary float float two),
    foreignBinding "less_equal_float" (binary float float two),
    foreignBinding "text_to_float" (unary text (option float)),
    foreignBinding "equal_natural" (binary natural natural two),
    foreignBinding "less_equal_natural" (binary natural natural two),
    foreignBinding "add_natural" (binary natural natural natural),
    foreignBinding "multiply_natural" (binary natural natural natural),
    foreignBinding "divide_remainder_natural" (binary natural natural (option (product natural natural))),
    foreignBinding "natural_to_text" (unary natural text),
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
    unicode = HostCon "unicode"
    text = HostCon "text"
    two = HostCon (canonicalDataTypeName twoData)
    one = HostCon (canonicalDataTypeName oneData)
    variable = HostVar
    action value = HostApp "deed" [value]
    task value = HostApp "task" [value]
    outcome value = HostApp (canonicalDataTypeName sumData) [text, value]
    deed name variables arguments result = foreignBinding name (HostSignature variables arguments result)
    list value = HostApp (canonicalDataTypeName listData) [value]
    option value = HostApp (canonicalDataTypeName optionData) [value]
    product left right = HostApp (canonicalDataTypeName productData) [left, right]

foreignBinding :: String -> HostSignature -> HostBinding
foreignBinding = HostBinding

unary :: HostType -> HostType -> HostSignature
unary argument = HostSignature [] [argument]

binary :: HostType -> HostType -> HostType -> HostSignature
binary left right = HostSignature [] [left, right]

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
pureOperation = \case
  "natural_to_integer" -> unaryOperation \case HostNatural a -> Just (HostInteger (toInteger a)); _ -> Nothing
  "integer_to_natural" -> unaryOperation \case HostInteger a -> Just (HostOption (if a >= 0 then Just (HostNatural (fromInteger a)) else Nothing)); _ -> Nothing
  "add_natural" -> naturals \a b -> HostNatural (a + b)
  "subtract_natural" -> naturals \a b -> HostNatural (if b > a then 0 else a - b)
  "multiply_natural" -> naturals \a b -> HostNatural (a * b)
  "divide_remainder_natural" -> naturals \a b -> HostOption (if b == 0 then Nothing else Just (HostPair (HostNatural (a `div` b)) (HostNatural (a `mod` b))))
  "equal_natural" -> naturals \a b -> HostTruth (a == b)
  "less_equal_natural" -> naturals \a b -> HostTruth (a <= b)
  "natural_to_text" -> unaryOperation \case HostNatural a -> Just (HostText (show a)); _ -> Nothing
  "add_integer" -> integers \a b -> HostInteger (a + b)
  "subtract_integer" -> integers \a b -> HostInteger (a - b)
  "multiply_integer" -> integers \a b -> HostInteger (a * b)
  "divide_remainder_integer" -> integers \a b -> HostOption (if b == 0 then Nothing else Just (let (q, r) = euclidean a b in HostPair (HostInteger q) (HostInteger r)))
  "equal_integer" -> integers \a b -> HostTruth (a == b)
  "less_equal_integer" -> integers \a b -> HostTruth (a <= b)
  "integer_to_text" -> unaryOperation \case HostInteger a -> Just (HostText (show a)); _ -> Nothing
  "add_float" -> floats \a b -> HostFloat (a + b)
  "subtract_float" -> floats \a b -> HostFloat (a - b)
  "multiply_float" -> floats \a b -> HostFloat (a * b)
  "divide_float" -> floats \a b -> HostFloat (a / b)
  -- þe angle of þe point (real, imaginary), in [0, 2π).
  "arctan_float" -> floats \real imaginary -> let angle = atan2 imaginary real in HostFloat (if angle < 0 then angle + 2 * pi else angle)
  "sine_float" -> floatUnary sin
  "exponent_float" -> floatUnary exp
  "logariþm_float" -> floatUnary log
  "⌊" -> unaryOperation \case HostFloat a -> Just (HostOption (if isNaN a || isInfinite a then Nothing else Just (HostInteger (floor a)))); _ -> Nothing
  "equal_float" -> floats \a b -> HostTruth (a == b)
  "less_equal_float" -> floats \a b -> HostTruth (a <= b)
  "float_to_text" -> unaryOperation \case HostFloat a -> Just (HostText (show a)); _ -> Nothing
  "text_to_float" -> unaryOperation \case HostText a -> Just (HostOption (HostFloat <$> readMaybe a)); _ -> Nothing
  "unicode_to_natural" -> unaryOperation \case HostUnicode a -> Just (HostNatural (fromIntegral (ord a))); _ -> Nothing
  "natural_to_unicode" -> unaryOperation \case HostNatural a -> Just (HostOption (HostUnicode <$> unicodeScalar (toInteger a))); _ -> Nothing
  "equal_unicode" -> binaryOperation \case [HostUnicode a, HostUnicode b] -> Just (HostTruth (a == b)); _ -> Nothing
  "less_equal_unicode" -> binaryOperation \case [HostUnicode a, HostUnicode b] -> Just (HostTruth (a <= b)); _ -> Nothing
  "behead_text" -> unaryOperation \case HostText a -> Just (HostOption (case a of first : rest -> Just (HostPair (HostUnicode first) (HostText rest)); [] -> Nothing)); _ -> Nothing
  "text_to_list" -> unaryOperation \case HostText a -> Just (HostList (map HostUnicode a)); _ -> Nothing
  "list_to_text" -> unaryOperation \case HostList values -> HostText <$> traverse (\case HostUnicode a -> Just a; _ -> Nothing) values; _ -> Nothing
  "join_text" -> binaryOperation \case [HostText a, HostText b] -> Just (HostText (a ++ b)); _ -> Nothing
  "equal_text" -> binaryOperation \case [HostText a, HostText b] -> Just (HostTruth (a == b)); _ -> Nothing
  "less_equal_text" -> binaryOperation \case [HostText a, HostText b] -> Just (HostTruth (a <= b)); _ -> Nothing
  _ -> Nothing
  where
    unaryOperation f = Just \case [a] -> f a; _ -> Nothing
    binaryOperation = Just
    naturals f = binaryOperation \case [HostNatural a, HostNatural b] -> Just (f a b); _ -> Nothing
    integers f = binaryOperation \case [HostInteger a, HostInteger b] -> Just (f a b); _ -> Nothing
    floats f = binaryOperation \case [HostFloat a, HostFloat b] -> Just (f a b); _ -> Nothing
    floatUnary f = unaryOperation \case HostFloat a -> Just (HostFloat (f a)); _ -> Nothing
    -- þe remainder is never negative.
    euclidean a b =
      let (quotient, remainder) = a `divMod` b
       in if remainder < 0 then (quotient + 1, remainder - b) else (quotient, remainder)
