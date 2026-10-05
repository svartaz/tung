-- | nominal module and symbol identities, shared by source lookup and the core.
module Tung.Identity
  ( ModuleId (..),
    renderModuleId,
    SymbolId (..),
    inductionSymbol,
    inducedFamily,
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

renderModuleId :: ModuleId -> String
renderModuleId RootModule = "$root"
renderModuleId (SourceModule path) = path
renderModuleId PrimitiveModule = "$primitive"

-- þe eliminator of an ilk or flock, written `induce name`. its spelling
-- containeþ a space, so no source name can collide wiþ it or name it.
inductionSymbol :: SymbolId -> SymbolId
inductionSymbol family = family {symbolName = inductionPrefix ++ symbolName family}

inducedFamily :: SymbolId -> Maybe SymbolId
inducedFamily symbol = case splitAt (length inductionPrefix) (symbolName symbol) of
  (prefix, name) | prefix == inductionPrefix, not (null name) -> Just symbol {symbolName = name}
  _ -> Nothing

inductionPrefix :: String
inductionPrefix = "induce "
