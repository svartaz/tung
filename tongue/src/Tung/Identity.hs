-- | nominal module and symbol identities, shared by source lookup and the core.
module Tung.Identity
  ( ModuleId (..),
    SymbolId (..),
    inductionSymbol,
    inducedFamily,
    modelSymbol,
    modelledHost,
  )
where

-- primitive definitions belong to no source file.
data ModuleId = RootModule | SourceModule FilePath | PrimitiveModule
  deriving stock (Eq, Ord, Show)

data SymbolId = SymbolId
  { symbolModule :: ModuleId,
    symbolName :: String
  }
  deriving stock (Show)

-- names are compared before modules. module paths share long prefixes, and
-- global lookups compare identities constantly.
instance Eq SymbolId where
  SymbolId leftModule leftName == SymbolId rightModule rightName = leftName == rightName && leftModule == rightModule

instance Ord SymbolId where
  compare (SymbolId leftModule leftName) (SymbolId rightModule rightName) = compare leftName rightName <> compare leftModule rightModule

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
