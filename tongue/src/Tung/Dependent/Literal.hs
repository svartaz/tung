{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

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
    literalConstructor,
    constructedLiteral,
  )
where

import Control.DeepSeq (NFData)
import Data.Char (isControl, ord)
import Data.Maybe (fromMaybe)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import GHC.Generics (Generic)
import GHC.TypeLits (Natural)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Primitive (HostValue (..), hostTypeId, integerNegativeId, integerPositiveId, naturalSuccessorId, naturalZeroId, primitiveTypeNames)

-- floats are stored by bit pattern, so equality is reflexive even for NaN.
data HostLiteral
  = TextValue String
  | NaturalValue Natural
  | IntegerValue Integer
  | FloatBits Word64
  | UnicodeValue Char
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (NFData)

-- each literal inhabiteth a primitive type of the same name in every module.
literalType :: HostLiteral -> SymbolId
literalType =
  SymbolId PrimitiveModule . \case
    TextValue _ -> "string"
    NaturalValue _ -> "ℕ"
    IntegerValue _ -> "ℤ"
    FloatBits _ -> "float"
    UnicodeValue _ -> "unicode"

-- a structural literal readeth as its outer constructor and that
-- constructor's literal fields; 'constructedLiteral' is the inverse.
literalConstructor :: HostLiteral -> Maybe (SymbolId, [HostLiteral])
literalConstructor = \case
  NaturalValue 0 -> Just (naturalZeroId, [])
  NaturalValue value -> Just (naturalSuccessorId, [NaturalValue (value - 1)])
  IntegerValue value
    | value >= 0 -> Just (integerPositiveId, [NaturalValue (fromInteger value)])
    | otherwise -> Just (integerNegativeId, [NaturalValue (fromInteger (negate value - 1))])
  _ -> Nothing

constructedLiteral :: SymbolId -> [HostLiteral] -> Maybe HostLiteral
constructedLiteral constructor fields = case fields of
  [] | constructor == naturalZeroId -> Just (NaturalValue 0)
  [NaturalValue value]
    | constructor == naturalSuccessorId -> Just (NaturalValue (value + 1))
    | constructor == integerPositiveId -> Just (IntegerValue (toInteger value))
    | constructor == integerNegativeId -> Just (IntegerValue (negate (toInteger value) - 1))
  _ -> Nothing

literalTypeNames :: [String]
literalTypeNames = ["string", "ℕ", "ℤ", "float", "unicode"]

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

-- a catalogue type name nameth a primitive type or a declared host data type.
hostTypeSymbol :: String -> Maybe SymbolId
hostTypeSymbol name
  | name `elem` primitiveTypeNames = Just (SymbolId PrimitiveModule name)
  | otherwise = hostTypeId name

-- the ordinary checker qualifieth a constructor with its type, as `optional@some`;
-- the core nameth it alone. names never contain `@`.
coreConstructor :: SymbolId -> SymbolId
coreConstructor (SymbolId owner name) = SymbolId owner (drop 1 (dropWhile (/= '@') name))

-- a literal as source spelleth it.
renderLiteral :: HostLiteral -> String
renderLiteral = \case
  TextValue x -> "'" ++ concatMap (\character -> fromMaybe [character] (escaped character)) x ++ "'"
  NaturalValue x -> show x
  IntegerValue x -> (if x < 0 then "" else "+") ++ show x
  FloatBits x -> show (castWord64ToDouble x)
  UnicodeValue x -> '`' : fromMaybe (if isControl x then "\\" ++ show (ord x) ++ ";" else [x]) (escaped x)
  where
    escaped character = lookup character [('\n', "\\n"), ('\r', "\\r"), ('\t', "\\t"), ('\'', "\\'"), ('\\', "\\\\")]
