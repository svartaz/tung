-- | checked module state, visible names, exports, and class registries.
-- import aliases change visibility, while kernel identities remain fixed.
module Tung.Dependent.Source.Environment
  ( SourceProgram (..),
    sourceEnvironment,
    sourceExports,
    sourceHoles,
    Hole (..),
    Names (..),
    NameBinding (..),
    ClassInfo (..),
    lookupName,
    bindingSymbol,
    displayName,
    briefName,
    insertName,
    bindLocal,
    ambiguousName,
    repeated,
    symbolOf,
    mergeClass,
    registerClass,
    registerInstance,
    defaultPriority,
    exportIntroduced,
    reexportNames,
    typeOfName,
    sorryAssumptions,
    orsendAssumptions,
    sourceDefinitions,
    sourceGlobal,
    globals,
  )
where

import Control.Monad (foldM)
import Data.List (intercalate, nub)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Render (renderTermWith)
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Syntax
import Tung.Identity (ModuleId (..), SymbolId (..), inducedFamily)
import Tung.Name qualified as Name
import Tung.Token (SourceFailure, SourceSpan)

data SourceProgram = SourceProgram
  { programEnvironment :: K.Environment,
    checkedDefinitions :: [(SymbolId, K.Inferred)],
    -- visible names: local definitions, qualified imports, and unambiguous
    -- bare imports. local definitions shadow bare imports.
    globalNames :: Names,
    localNames :: Set.Set String,
    programExports :: Names,
    -- þe goal and named context of each `sorry` in þis module, newest first.
    programHoles :: [Hole]
  }
  deriving stock (Eq, Show)

-- public accessors are ordinary functions. an exported record selector would
-- let callers replace a checked environment even wiþ its constructor hidden.
sourceEnvironment :: SourceProgram -> K.Environment
sourceEnvironment = programEnvironment

sourceExports :: SourceProgram -> Names
sourceExports = programExports

sourceHoles :: SourceProgram -> [Hole]
sourceHoles = programHoles

data Hole = Hole
  { holeSpan :: Maybe SourceSpan,
    holeGoal :: String,
    -- named locals, outermost first, wiþ þeir types.
    holeContext :: [(String, String)]
  }
  deriving stock (Eq, Show)

data NameBinding
  = FreshName SymbolId Int
  | FixedName SymbolId [Level]
  | -- a bare name shown by several imports; qualification selecteþ one.
    AmbiguousName [String]
  deriving stock (Eq, Show)

-- visible names and the instances registered for each class family. every
-- class hath an entry, so membership also identifieþ dictionary types.
data Names = Names
  { nameTable :: Map.Map String NameBinding,
    nameClasses :: Map.Map SymbolId ClassInfo
  }
  deriving stock (Eq, Show)

-- a class is a one-constructor family. its implicit fields hold parent
-- dictionaries; its explicit fields are the members, in declaration order.
data ClassInfo = ClassInfo
  { classConstructor :: SymbolId,
    classMembers :: [String],
    -- parent classes, which an instance's dictionary also needeþ.
    classParents :: [SymbolId],
    -- registered instances, oldest first. they outrank inherited instances.
    classInstances :: [SymbolId],
    -- instances that project this class from a child class's dictionary.
    classInherited :: [SymbolId],
    -- each registered instance's written priority; þe default is
    -- 'defaultPriority'. search trieþ higher priorities first, as lean doþ.
    classPriorities :: Map.Map SymbolId Integer,
    -- for each flock parameter, wheþer instance search findeþ it (`* out`)
    -- raþer þan requiring it known, as lean's `outParam` doþ.
    classOutputs :: [Bool],
    -- instances written `bizen fallback`, tried only for a goal whose
    -- inputs stay unknown, as lean's `default_instance` is.
    classFallbacks :: [SymbolId]
  }
  deriving stock (Eq, Show)

mergeClass :: ClassInfo -> ClassInfo -> ClassInfo
mergeClass left right =
  left
    { classInstances = nub (classInstances left ++ classInstances right),
      classInherited = nub (classInherited left ++ classInherited right),
      classPriorities = Map.union (classPriorities left) (classPriorities right),
      classFallbacks = nub (classFallbacks left ++ classFallbacks right)
    }

-- instances are global, so registration also exporteþ them wherever the
-- class itself is visible to importers.
registerInstance :: Bool -> (Integer, Bool) -> SymbolId -> SymbolId -> SourceProgram -> SourceProgram
registerInstance inherited (priority, fallback) family instanceSymbol program@SourceProgram {globalNames, programExports} =
  program {globalNames = add globalNames, programExports = add programExports}
  where
    add names = names {nameClasses = Map.adjust register family (nameClasses names)}
    register info
      | inherited = info {classInherited = nub (classInherited info ++ [instanceSymbol])}
      | otherwise =
          info
            { classInstances = nub (classInstances info ++ [instanceSymbol]),
              classPriorities = Map.insert instanceSymbol priority (classPriorities info),
              classFallbacks = [instanceSymbol | fallback] ++ classFallbacks info
            }

-- þe priority of a bizen written wiþout one, as in lean.
defaultPriority :: Integer
defaultPriority = 1000

lookupName :: String -> Names -> Maybe NameBinding
lookupName name = Map.lookup name . nameTable

-- imported identities print through a visible qualified alias; local and
-- primitive identities retain their bare names. aliases never change equality.
displayName :: Names -> SymbolId -> String
displayName names identity | Just family <- inducedFamily identity = "unbuild " ++ displayName names family
displayName Names {nameTable} identity = case qualified of
  name : _ -> name
  [] -> symbolName identity
  where
    qualified = [name | (name, binding) <- Map.toList nameTable, '~' `elem` name, matches binding]
    matches binding = bindingSymbol binding == Just identity

-- goals prefer a visible bare name; an identity wiþout one printeþ as
-- 'displayName' doþ.
briefName :: Names -> SymbolId -> String
briefName names identity | Just family <- inducedFamily identity = "unbuild " ++ briefName names family
briefName names@Names {nameTable} identity = case [name | (name, binding) <- Map.toList nameTable, '~' `notElem` name, bindingSymbol binding == Just identity] of
  name : _ -> name
  [] -> displayName names identity

insertName :: String -> NameBinding -> Names -> Names
insertName name binding names = names {nameTable = Map.insert name binding (nameTable names)}

bindingSymbol :: NameBinding -> Maybe SymbolId
bindingSymbol (FreshName identity _) = Just identity
bindingSymbol (FixedName identity _) = Just identity
bindingSymbol (AmbiguousName _) = Nothing

ambiguousName :: String -> [String] -> String
ambiguousName name modules = "ambiguous name '" ++ name ++ "' is shown by " ++ intercalate " and " [space ++ "~" ++ name | space <- modules] ++ "; qualify it"

bindLocal :: String -> NameBinding -> SourceProgram -> SourceProgram
bindLocal name binding program@SourceProgram {..} =
  program {globalNames = insertName name binding globalNames, localNames = Set.insert name localNames}

-- types, classes, constructors, members, and definitions share one namespace.
repeated :: Set.Set String -> [String] -> Either SourceFailure ()
repeated declared names = case [name | (index, name) <- zip [0 :: Int ..] names, name `Set.member` declared || name `elem` take index names] of
  name : _ -> Error.failure ("top-level name repeateþ '" ++ name ++ "'")
  [] -> pure ()

symbolOf :: String -> SourceProgram -> Either SourceFailure SymbolId
symbolOf name SourceProgram {globalNames} = case lookupName name globalNames of
  Just (FreshName symbol _) -> pure symbol
  _ -> Error.failure ("missing generated name '" ++ name ++ "'")

registerClass :: SymbolId -> ClassInfo -> Names -> Names
registerClass symbol info names = names {nameClasses = Map.insertWith keep symbol info (nameClasses names)}
  where
    keep _ existing = existing

-- a shown declaration exporteþ the names and class metadata it introduceþ.
exportIntroduced :: SourceProgram -> SourceProgram -> SourceProgram
exportIntroduced before after@SourceProgram {globalNames, programExports} =
  let introduced = Set.difference (localNames after) (localNames before)
      exported = Map.restrictKeys (nameTable globalNames) introduced
      shownClasses = Map.filter (\ClassInfo {classConstructor} -> symbolName classConstructor `Set.member` introduced) (nameClasses globalNames)
   in after {programExports = programExports {nameTable = Map.union exported (nameTable programExports), nameClasses = Map.unionWith mergeClass (nameClasses programExports) shownClasses}}

-- re-exported names keep their identities and class registries. a qualified
-- source name is shown under its last segment.
reexportNames :: SourceProgram -> [String] -> Either SourceFailure SourceProgram
reexportNames = foldM reexport
  where
    reexport current@SourceProgram {globalNames, programExports} name = case lookupName name globalNames of
      Just (AmbiguousName namespaces) -> Error.failure (ambiguousName name namespaces)
      Just binding
        | Just identity <- bindingSymbol binding ->
            pure
              current
                { programExports =
                    programExports
                      { nameTable = Map.insert (Name.lastQualifiedSegment name) binding (nameTable programExports),
                        nameClasses = maybe id (Map.insertWith mergeClass identity) (Map.lookup identity (nameClasses globalNames)) (nameClasses programExports)
                      }
                }
      _ -> Error.failure ("cannot show unknown name '" ++ name ++ "'")

-- þe module's shown declarations, bizens, and `main` þat depend on
-- `sorry`, directly or þrough any definition þeir bodies use; a bizen wiþ a
-- law proved by `sorry` is one. a host binding is a program, not an
-- assumption.
sorryAssumptions :: SourceProgram -> [String]
sorryAssumptions SourceProgram {..} =
  [describe symbol | (symbol, _) <- reverse checkedDefinitions, reported symbol, assumes symbol]
  where
    definitions = globals programEnvironment
    -- definitions may refer to þemselves, so þe search walkeþ backwards
    -- from `sorry` through þe users of each definition.
    users = Map.fromListWith (++) [(used, [user]) | (user, Definition {definitionBody = Transparent term}) <- Map.toList definitions, used <- nub (termGlobals term)]
    reach seen [] = seen
    reach seen (symbol : rest)
      | symbol `Set.member` seen = reach seen rest
      | otherwise = reach (Set.insert symbol seen) (Map.findWithDefault [] symbol users ++ rest)
    assuming = reach Set.empty [SymbolId PrimitiveModule "sorry"]
    assumes symbol = symbol `Set.member` assuming
    shown = Set.fromList [symbol | binding <- Map.elems (nameTable programExports), Just symbol <- [bindingSymbol binding]]
    reported symbol = symbol `Set.member` shown || isInstance symbol || symbolName symbol == "main"
    isInstance symbol = take 10 (symbolName symbol) == "#instance_"
    describe symbol
      | isInstance symbol = "bizen " ++ maybe "?" (renderTermWith (displayName globalNames) [] . definitionType) (Map.lookup symbol definitions)
      | otherwise = displayName globalNames symbol

-- þe module's own `orsend` assumptions, each wiþ its type.
orsendAssumptions :: SourceProgram -> [String]
orsendAssumptions SourceProgram {..} =
  [ name ++ ": " ++ renderTermWith (displayName globalNames) [] definitionType
  | name <- Set.toList localNames,
    Just symbol <- [lookupName name globalNames >>= bindingSymbol],
    Just Definition {definitionType, definitionBody = Assumption} <- [Map.lookup symbol (globals programEnvironment)]
  ]

termGlobals :: Term -> [SymbolId]
termGlobals = \case
  Global symbol _ -> [symbol]
  term -> concatMap (termGlobals . snd) (children term)

typeOfName :: SourceProgram -> String -> Either String String
typeOfName SourceProgram {..} name = case lookupName name globalNames of
  Just (AmbiguousName modules) -> Left (ambiguousName name modules)
  binding -> maybe (Left ("unknown name '" ++ name ++ "'")) found (binding >>= bindingSymbol)
  where
    found identity = maybe (Left ("unknown name '" ++ name ++ "'")) (Right . renderTermWith (displayName globalNames) [] . definitionType) (Map.lookup identity (globals programEnvironment))

sourceDefinitions :: SourceProgram -> [(SymbolId, K.Inferred)]
sourceDefinitions = reverse . checkedDefinitions

-- top-level names resolve after every declaration hath been checked.
sourceGlobal :: SourceProgram -> String -> Maybe SymbolId
sourceGlobal SourceProgram {globalNames} name = lookupName name globalNames >>= bindingSymbol

globals :: K.Environment -> Globals
globals (K.Environment definitions) = definitions
