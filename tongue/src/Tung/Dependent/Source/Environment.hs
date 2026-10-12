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
    exportNames,
    reexportNames,
    typeOfName,
    sorryAssumptions,
    orsendAssumptions,
    sourceDefinitions,
    sourceGlobal,
    globals,
    internProgram,
    internNames,
  )
where

import Control.Monad (foldM)
import Data.List (intercalate, nub)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Render (renderTermIn)
import Tung.Dependent.Syntax
import Tung.Identity (ModuleId (..), SymbolId (..), inducedFamily, internSymbols, modelledHost)
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
    -- the goal and named context of each `sorry` in this module, newest first.
    programHoles :: [Hole],
    -- resolved source references survive computation during elaboration.
    programReferences :: Map.Map SymbolId (Set.Set SymbolId)
  }
  deriving stock (Eq, Show)

-- only this module's new definitions are walked. imported definition bodies
-- and map subtrees remain shared with their checked modules.
internProgram :: Globals -> SourceProgram -> SourceProgram
internProgram imported program@SourceProgram {..} =
  program
    { programEnvironment = K.Environment (Map.union own imported),
      checkedDefinitions = [(intern symbol, checked symbol) | (symbol, _) <- checkedDefinitions],
      globalNames = internNames intern globalNames,
      programExports = internNames intern programExports,
      programReferences = Map.union (Map.mapKeysMonotonic intern (Map.map (Set.mapMonotonic intern) ownReferences)) inheritedReferences
    }
  where
    definitions = globals programEnvironment
    intern = internSymbols definitions
    own = Map.map (mapDefinitionSymbols intern) (Map.difference definitions imported)
    ownReferences = Map.restrictKeys programReferences (Map.keysSet own)
    inheritedReferences = Map.withoutKeys programReferences (Map.keysSet own)
    -- recorded source definitions are this module's transparent constants.
    -- reuse their rewritten trees rather than retaining and walking them twice.
    checked symbol = case own Map.! symbol of
      Definition {definitionUniverses, definitionConstraints, definitionType, definitionBody = Transparent term} ->
        K.Inferred definitionUniverses definitionConstraints term definitionType
      _ -> error "recorded source definition is not transparent"

-- the supplied interner preserveth identity and therefore map ordering.
-- visible names retain their spelling; only resolved identities are shared.
internNames :: (SymbolId -> SymbolId) -> Names -> Names
internNames intern Names {nameTable, nameClasses} =
  Names (Map.map binding nameTable) (Map.mapKeysMonotonic intern (Map.map registry nameClasses))
  where
    binding = \case
      FreshName symbol universes -> FreshName (intern symbol) universes
      FixedName symbol levels -> FixedName (intern symbol) levels
      ambiguous@AmbiguousName {} -> ambiguous
    registry info@ClassInfo {..} =
      info
        { classParents = map intern classParents,
          classInstances = map intern classInstances,
          classInherited = map intern classInherited,
          classPriorities = Map.mapKeysMonotonic intern classPriorities,
          classFallbacks = map intern classFallbacks
        }

-- public accessors are ordinary functions. an exported record selector would
-- let callers replace a checked environment even with its constructor hidden.
sourceEnvironment :: SourceProgram -> K.Environment
sourceEnvironment = programEnvironment

sourceExports :: SourceProgram -> Names
sourceExports = programExports

sourceHoles :: SourceProgram -> [Hole]
sourceHoles = programHoles

data Hole = Hole
  { holeSpan :: Maybe SourceSpan,
    holeGoal :: String,
    -- named locals, outermost first, with their types.
    holeContext :: [(String, String)]
  }
  deriving stock (Eq, Show)

data NameBinding
  = FreshName SymbolId Int
  | FixedName SymbolId [Level]
  | -- a bare name shown by several imports; qualification selecteth one.
    AmbiguousName [String]
  deriving stock (Eq, Show)

-- visible names and the instances registered for each class family. every
-- class hath an entry, so membership also identifieth dictionary types.
data Names = Names
  { nameTable :: Map.Map String NameBinding,
    nameClasses :: Map.Map SymbolId ClassInfo
  }
  deriving stock (Eq, Show)

-- a class is a one-constructor family. its implicit fields hold parent
-- dictionaries; its explicit fields are the members, in declaration order.
data ClassInfo = ClassInfo
  { classMembers :: [String],
    -- parent classes, which an instance's dictionary also needeth.
    classParents :: [SymbolId],
    -- registered instances, oldest first. they outrank inherited instances.
    classInstances :: [SymbolId],
    -- instances that project this class from a child class's dictionary.
    classInherited :: [SymbolId],
    -- each registered instance's written priority; the default is
    -- 'defaultPriority'. search trieth higher priorities first, as lean doth.
    classPriorities :: Map.Map SymbolId Integer,
    -- for each flock parameter, whether instance search findeth it (`* out`)
    -- rather than requiring it known, as lean's `outParam` doth.
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

-- instances are global, so registration also exporteth them wherever the
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

-- the priority of a bizen written without one, as in lean.
defaultPriority :: Integer
defaultPriority = 1000

lookupName :: String -> Names -> Maybe NameBinding
lookupName name = Map.lookup name . nameTable

-- imported identities print through a visible qualified alias; local and
-- primitive identities retain their bare names. aliases never change equality.
displayName :: Names -> SymbolId -> String
displayName names identity | Just family <- inducedFamily identity = "unbuild " ++ displayName names family
displayName names identity | Just host <- modelledHost identity = displayName names host
displayName Names {nameTable} identity = case qualified of
  name : _ -> name
  [] -> symbolName identity
  where
    qualified = [name | (name, binding) <- Map.toList nameTable, '~' `elem` name, matches binding]
    matches binding = bindingSymbol binding == Just identity

-- goals prefer a visible bare name; an identity without one printeth as
-- 'displayName' doth.
briefName :: Names -> SymbolId -> String
briefName names identity | Just family <- inducedFamily identity = "unbuild " ++ briefName names family
briefName names identity | Just host <- modelledHost identity = briefName names host
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
  name : _ -> Error.failure ("top-level name repeateth '" ++ name ++ "'")
  [] -> pure ()

symbolOf :: String -> SourceProgram -> Either SourceFailure SymbolId
symbolOf name SourceProgram {globalNames} = case lookupName name globalNames of
  Just (FreshName symbol _) -> pure symbol
  _ -> Error.failure ("missing generated name '" ++ name ++ "'")

registerClass :: SymbolId -> ClassInfo -> Names -> Names
registerClass symbol info names = names {nameClasses = Map.insertWith keep symbol info (nameClasses names)}
  where
    keep _ existing = existing

-- a shown declaration exporteth the names and class metadata it introduceth.
exportIntroduced :: SourceProgram -> SourceProgram -> SourceProgram
exportIntroduced before after = exportNames (Set.difference (localNames after) (localNames before)) after

-- group insertion exporteth only the names of its individually shown members.
exportNames :: Set.Set String -> SourceProgram -> SourceProgram
exportNames introduced after@SourceProgram {globalNames, programExports} =
  let exported = Map.restrictKeys (nameTable globalNames) introduced
      shownClasses = Map.restrictKeys (nameClasses globalNames) (Set.fromList [symbol | binding <- Map.elems exported, Just symbol <- [bindingSymbol binding]])
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

-- the module's shown declarations, bizens, and `main` that depend on
-- `sorry`, directly or through any definition their bodies use; a bizen with a
-- law proved by `sorry` is one. a host binding is a program, not an
-- assumption.
sorryAssumptions :: SourceProgram -> [String]
sorryAssumptions SourceProgram {..} =
  [describe symbol | (symbol, _) <- reverse checkedDefinitions, reported symbol, assumes symbol]
  where
    definitions = globals programEnvironment
    -- definitions may refer to themselves, so the search walketh backwards
    -- from `sorry` through the users of each definition.
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
      | isInstance symbol = "bizen " ++ maybe "?" (renderTermIn definitions (displayName globalNames) K.emptyContext [] . definitionType) (Map.lookup symbol definitions)
      | otherwise = displayName globalNames symbol

-- the module's own `orsetting` assumptions, each with its type.
orsendAssumptions :: SourceProgram -> [String]
orsendAssumptions SourceProgram {..} =
  [ name ++ ": " ++ render definitionType
  | name <- Set.toList localNames,
    Just symbol <- [lookupName name globalNames >>= bindingSymbol],
    Just Definition {definitionType, definitionBody = Assumption} <- [Map.lookup symbol (globals programEnvironment)]
  ]
  where
    render = renderTermIn (globals programEnvironment) (displayName globalNames) K.emptyContext []

termGlobals :: Term -> [SymbolId]
termGlobals = \case
  Global symbol _ -> [symbol]
  term -> concatMap (termGlobals . snd) (children term)

typeOfName :: SourceProgram -> String -> Either String String
typeOfName SourceProgram {..} name = case lookupName name globalNames of
  Just (AmbiguousName modules) -> Left (ambiguousName name modules)
  binding -> maybe (Left ("unknown name '" ++ name ++ "'")) found (binding >>= bindingSymbol)
  where
    render = renderTermIn (globals programEnvironment) (displayName globalNames) K.emptyContext []
    found identity = maybe (Left ("unknown name '" ++ name ++ "'")) (Right . render . definitionType) (Map.lookup identity (globals programEnvironment))

sourceDefinitions :: SourceProgram -> [(SymbolId, K.Inferred)]
sourceDefinitions = reverse . checkedDefinitions

-- top-level names resolve after every declaration hath been checked.
sourceGlobal :: SourceProgram -> String -> Maybe SymbolId
sourceGlobal SourceProgram {globalNames} name = lookupName name globalNames >>= bindingSymbol

globals :: K.Environment -> Globals
globals (K.Environment definitions) = definitions
