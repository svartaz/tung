{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}

-- | nominal module and symbol identities, shared by source lookup and the core.
module Tung.Identity
  ( ModuleId (..),
    SymbolId (SymbolId, symbolModule, symbolName),
    internSymbols,
    inductionSymbol,
    inducedFamily,
    modelSymbol,
    modelledHost,
  )
where

import Data.Bits (xor)
import Data.Char (ord)
import Data.Map.Strict qualified as Map
import GHC.Exts (isTrue#, reallyUnsafePtrEquality#)

-- primitive definitions belong to no source file.
data ModuleId = RootModule | SourceModule FilePath | PrimitiveModule
  deriving stock (Eq, Ord, Show)

-- an identity carrieth a hash of its name, computed once when it is built.
-- global lookups compare identities constantly; equal hashes are rare, so
-- most comparisons never walk the name or the long module path.
data SymbolId = SymbolIdHashed !Int ModuleId String

pattern SymbolId :: ModuleId -> String -> SymbolId
pattern SymbolId {symbolModule, symbolName} <- SymbolIdHashed _ symbolModule symbolName
  where
    SymbolId owner name = SymbolIdHashed (nameHash name) owner name

{-# COMPLETE SymbolId #-}

-- fnv-1a over the name's characters.
nameHash :: String -> Int
nameHash = foldl' (\hash character -> (hash `xor` ord character) * 16777619) 2166136261

instance Show SymbolId where
  showsPrec depth (SymbolId owner name) =
    showParen (depth >= 11) $
      showString "SymbolId {symbolModule = " . showsPrec 0 owner . showString ", symbolName = " . showsPrec 0 name . showString "}"

instance Eq SymbolId where
  left@(SymbolIdHashed leftHash leftModule leftName) == right@(SymbolIdHashed rightHash rightModule rightName) =
    shared left right || leftHash == rightHash && same leftName rightName && same leftModule rightModule

-- the order is by hash, then name, then module: any total order serveth maps.
-- a found lookup endeth in equal identities, whose names and modules are
-- usually the very values a module's checking shared, so a pointer test
-- skippeth walking the long module path.
instance Ord SymbolId where
  compare left@(SymbolIdHashed leftHash leftModule leftName) right@(SymbolIdHashed rightHash rightModule rightName)
    | shared left right = EQ
    | otherwise = compare leftHash rightHash <> ordered leftName rightName <> ordered leftModule rightModule
    where
      ordered left right = if shared left right then EQ else compare left right

same :: (Eq a) => a -> a -> Bool
same left right = shared left right || left == right

shared :: a -> a -> Bool
shared left right = isTrue# (reallyUnsafePtrEquality# left right)

-- reuse an environment's keys, without a process-wide pool. values hold only
-- identities, so a delayed traversal cannot retain the original definitions.
-- absent identities retain their nominal meaning; interning never changeth
-- equality or ordering, so maps may retain their existing key order.
internSymbols :: Map.Map SymbolId a -> SymbolId -> SymbolId
internSymbols symbols = \symbol -> Map.findWithDefault symbol symbol canonical
  where
    canonical = Map.mapWithKey (\symbol _ -> symbol) symbols

-- the eliminator of an ilk or flock, written `unbuild name`. its spelling
-- containeth a space, so no source name can collide with it or name it.
inductionSymbol :: SymbolId -> SymbolId
inductionSymbol family = family {symbolName = inductionPrefix ++ symbolName family}

inducedFamily :: SymbolId -> Maybe SymbolId
inducedFamily symbol = case splitAt (length inductionPrefix) (symbolName symbol) of
  (prefix, name) | prefix == inductionPrefix, not (null name) -> Just symbol {symbolName = name}
  _ -> Nothing

-- the structural model of a host binding. it is the same function, so goals
-- print it under the binding's name; the space keepeth it out of source.
modelSymbol :: SymbolId -> SymbolId
modelSymbol host = host {symbolName = modelPrefix ++ symbolName host}

modelledHost :: SymbolId -> Maybe SymbolId
modelledHost symbol = case splitAt (length modelPrefix) (symbolName symbol) of
  (prefix, name) | prefix == modelPrefix, not (null name) -> Just symbol {symbolName = name}
  _ -> Nothing

modelPrefix :: String
modelPrefix = "model "

inductionPrefix :: String
inductionPrefix = "unbuild "
