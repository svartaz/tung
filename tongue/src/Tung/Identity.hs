{-# LANGUAGE PatternSynonyms #-}

-- | nominal module and symbol identities, shared by source lookup and the core.
module Tung.Identity
  ( ModuleId (..),
    SymbolId (SymbolId, symbolModule, symbolName),
    inductionSymbol,
    inducedFamily,
    modelSymbol,
    modelledHost,
  )
where

import Data.Bits (xor)
import Data.Char (ord)
import Data.List (foldl')

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
  SymbolIdHashed leftHash leftModule leftName == SymbolIdHashed rightHash rightModule rightName =
    leftHash == rightHash && leftName == rightName && leftModule == rightModule

-- the order is by hash, then name, then module: any total order serveth maps.
instance Ord SymbolId where
  compare (SymbolIdHashed leftHash leftModule leftName) (SymbolIdHashed rightHash rightModule rightName) =
    compare leftHash rightHash <> compare leftName rightName <> compare leftModule rightModule

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
