-- | host literal values and their bridge to the shared host catalogue. the
-- kernel's normaliser and the runner compute pure host operations through
-- 'Tung.Primitive.pureOperation', so checking-time computation and execution
-- cannot disagree.
module Tung.Dependent.Literal
  ( HostLiteral (..),
    literalType,
    literalTypeNames,
    literalValue,
    valueLiteral,
    hostTypeSymbol,
    coreConstructor,
    renderLiteral,
  )
where

import Control.DeepSeq (NFData (..))
import Data.Char (isControl, ord)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import GHC.TypeLits (Natural)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Primitive (HostValue (..), hostTypeId, primitiveTypeNames)

-- floats are stored by bit pattern, so equality is reflexive even for NaN.
data HostLiteral
  = TextValue String
  | NaturalValue Natural
  | IntegerValue Integer
  | FloatBits Word64
  | UnicodeValue Char
  deriving stock (Eq, Ord, Show)

instance NFData HostLiteral where
  rnf = \case
    TextValue x -> rnf x
    NaturalValue x -> rnf x
    IntegerValue x -> rnf x
    FloatBits x -> rnf x
    UnicodeValue x -> rnf x

-- each literal inhabiteþ a primitive type of þe same name in every module.
literalType :: HostLiteral -> SymbolId
literalType =
  SymbolId PrimitiveModule . \case
    TextValue _ -> "text"
    NaturalValue _ -> "ℕ"
    IntegerValue _ -> "ℤ"
    FloatBits _ -> "float"
    UnicodeValue _ -> "unicode"

literalTypeNames :: [String]
literalTypeNames = ["text", "ℕ", "ℤ", "float", "unicode"]

literalValue :: HostLiteral -> HostValue
literalValue = \case
  TextValue x -> HostText x
  NaturalValue x -> HostNatural x
  IntegerValue x -> HostInteger x
  FloatBits x -> HostFloat (castWord64ToDouble x)
  UnicodeValue x -> HostUnicode x

-- only a host value of a primitive type is a literal.
valueLiteral :: HostValue -> Maybe HostLiteral
valueLiteral = \case
  HostText x -> Just (TextValue x)
  HostNatural x -> Just (NaturalValue x)
  HostInteger x -> Just (IntegerValue x)
  HostFloat x -> Just (FloatBits (castDoubleToWord64 x))
  HostUnicode x -> Just (UnicodeValue x)
  _ -> Nothing

-- a catalogue type name nameþ a primitive type or a declared host data type.
hostTypeSymbol :: String -> Maybe SymbolId
hostTypeSymbol name
  | name `elem` primitiveTypeNames = Just (SymbolId PrimitiveModule name)
  | otherwise = hostTypeId name

-- þe ordinary checker qualifieþ a constructor wiþ its type, as `option@some`;
-- þe core nameþ it alone. names never contain `@`.
coreConstructor :: SymbolId -> SymbolId
coreConstructor (SymbolId owner name) = SymbolId owner (drop 1 (dropWhile (/= '@') name))

-- a literal as source spelleþ it.
renderLiteral :: HostLiteral -> String
renderLiteral = \case
  TextValue x -> "'" ++ concatMap (\character -> maybe [character] id (escaped character)) x ++ "'"
  NaturalValue x -> show x
  IntegerValue x -> (if x < 0 then "" else "+") ++ show x
  FloatBits x -> show (castWord64ToDouble x)
  UnicodeValue x -> '`' : maybe (if isControl x then "\\" ++ show (ord x) ++ ";" else [x]) id (escaped x)
  where
    escaped character = lookup character [('\n', "\\n"), ('\r', "\\r"), ('\t', "\\t"), ('\'', "\\'"), ('\\', "\\\\")]
