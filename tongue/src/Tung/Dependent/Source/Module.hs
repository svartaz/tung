-- | import graphs, namespace assembly, and declaration scheduling.
-- declaration checking is supplied by elaboration; this module doth not
-- inspect metavariables, normalise terms, or select instances.
module Tung.Dependent.Source.Module
  ( compileProject,
    compileImports,
    recoverModule,
    moduleEnvironment,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (foldM, foldM_, forM, forM_)
import Data.Bifunctor (first)
import Data.Graph (SCC (..), flattenSCC, stronglyConnComp)
import Data.List (intercalate, nub, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing, listToMaybe)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Instance (sameInstance)
import Tung.Dependent.Source.Parse (SourceSnapshot (..))
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax (Definition (..), Plicity (..), Term (..))
import Tung.Identity (ModuleId (..), SymbolId (..), inducedFamily)
import Tung.Name qualified as Name
import Tung.Token (SourceFailure, SourceSpan)

-- the only connection to elaboration. a successful declaration group returneth an
-- updated, kernel-checked module; import loading cannot bypass that check.
type CheckDeclarations = ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Either SourceFailure SourceProgram

parsed :: SourceSnapshot -> Either CompileFailure ([(Maybe SourceSpan, Declaration)], Maybe Expression)
parsed = Error.compilationFailure ParseFailure . snapshotProgram

-- a root may yield an expression. its checking and execution belong to the
-- source facade, after every reachable declaration hath been checked.
compileProject :: CheckDeclarations -> Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Either CompileFailure (SourceProgram, Maybe Expression)
compileProject check compiled owner source modules = do
  (declarations, yielded) <- parsed source
  done <- compileImportsAt check compiled modules (importEdges declarations)
  program <- compileModule check owner declarations done
  pure (program, yielded)

-- precompiled modules are authoritative and are never reloaded. every other
-- reached module is compiled once, with its dependencies available first.
compileImports :: CheckDeclarations -> Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImports check compiled modules = compileImportsAt check compiled modules . map (Nothing,)

compileImportsAt :: CheckDeclarations -> Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [(Maybe SourceSpan, String)] -> Either CompileFailure (Map.Map String SourceProgram)
compileImportsAt check compiled modules = foldM (compileImport []) compiled
  where
    compileImport stack done (span, path)
      | Map.member path done = pure done
      | path `elem` stack = Left (CompileFailure CheckFailure Nothing span ("bring cycle: " ++ intercalate " -> " (reverse (path : stack))))
      | otherwise = do
          -- an absent source and a cycle are faults in the importing module,
          -- so neither may acquire the missing or repeated module's path.
          imported <- maybe (Left (CompileFailure CheckFailure Nothing span ("missing bring '" ++ path ++ "'"))) Right (Map.lookup path modules)
          inModule path do
            (declarations, _) <- parsed imported
            done' <- foldM (compileImport (path : stack)) done (importEdges declarations)
            program <- compileModule check (SourceModule path) declarations done'
            pure (Map.insert path program done')
    -- the innermost existing module keepeth its path; outer modules extend the
    -- message without changing the owner or source span.
    inModule path = first (\failure -> failure {failurePath = failurePath failure <|> Just path, failureText = "in bring '" ++ path ++ "': " ++ failureText failure})

importEdges :: [(Maybe SourceSpan, Declaration)] -> [(Maybe SourceSpan, String)]
importEdges declarations = [(span, importPath) | (span, ImportDeclaration {importPath}) <- declarations]

compileModule :: CheckDeclarations -> ModuleId -> [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Either CompileFailure SourceProgram
compileModule check owner declarations compiled = do
  initial <- moduleEnvironment declarations compiled
  batches <- orderDeclarations initial declarations
  let insert program batch = Error.compilationFailure CheckFailure (check owner program batch)
  internProgram (globals (sourceEnvironment initial)) <$> foldM insert initial batches

-- a diagnostic pass useth only fully checked imports and declaration groups.
-- rejected groups and every group depending on them are skipped atomically.
-- this partial environment is private to recovery and cannot be audited or run.
recoverModule :: (ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> (Either SourceFailure SourceProgram, Report)) -> ModuleId -> [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Maybe (SourceProgram, Report)
recoverModule check owner declarations compiled = do
  let available =
        filter
          ( \(_, declaration) -> case declaration of
              ImportDeclaration {importPath} -> Map.member importPath compiled
              _ -> True
          )
          declarations
  initial <- either (const Nothing) Just (moduleEnvironment available compiled)
  groups <- either (const Nothing) Just (declarationGroups initial available)
  let step (program, chunks, rejected) DeclarationGroup {..} =
        case groupFailure of
          Nothing
            | Set.disjoint groupRequired rejected ->
                let (result, found) = check owner program groupEntries
                 in case result of
                      Right next -> (next, found : chunks, rejected)
                      Left _ -> (hide groupEntries program, found : chunks, Set.union rejected groupIndices)
          _ -> (hide groupEntries program, chunks, Set.union rejected groupIndices)
      hide entries program = program {globalNames = (globalNames program) {nameTable = foldr Map.delete (nameTable (globalNames program)) (concatMap (defines . snd) entries)}}
      (program, chunks, _) = foldl step (initial, [], Set.empty) groups
  pure (program, mconcat (reverse chunks))

moduleEnvironment :: [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Either CompileFailure SourceProgram
moduleEnvironment declarations compiled = do
  imports <- forM [(span, path, alias) | (span, ImportDeclaration path alias) <- declarations] \(span, path, alias) ->
    (span,Name.importAlias path alias,path,) <$> maybe (Left (CompileFailure CheckFailure Nothing span ("missing bring '" ++ path ++ "'"))) Right (Map.lookup path compiled)
  -- every namespace nameth one module, including when an import is repeated.
  foldM_ claimNamespace Map.empty imports
  definitions <- foldM mergeGlobals H.primitiveDefinitions imports
  let qualified = Map.fromList [(space ++ "~" ++ name, binding) | (_, space, _, program) <- imports, (name, binding) <- Map.toList (nameTable (sourceExports program))]
      -- provenance is the visible import namespace, not the defining module.
      -- re-exports preserve identities but may arrive under different aliases.
      alternatives = Map.fromListWith (++) [(name, [(binding, space)]) | (_, space, _, program) <- imports, (name, binding) <- Map.toList (nameTable (sourceExports program))]
      resolve bindings = case nub (map fst bindings) of
        [binding] -> binding
        _ -> AmbiguousName (nub (map snd bindings))
      -- instances are global: every imported registry is merged.
      instances = Map.unionsWith mergeClass [nameClasses (sourceExports program) | (_, _, _, program) <- imports]
      -- imported and local names shadow primitive types.
      primitives = Map.fromList [(symbolName symbol, FreshName symbol (definitionUniverses definition)) | (symbol, definition) <- Map.toList H.primitiveDefinitions, symbol /= H.sorrySymbol, isNothing (inducedFamily symbol)]
      references = Map.unionsWith Set.union [programReferences program | (_, _, _, program) <- imports]
  -- bizens of one pattern from two imports would make selection depend on
  -- bring order. registration compareth only the bizens a module seeth, so
  -- those from different modules are compared again here.
  forM_ (Map.toList instances) \(family, ClassInfo {classInstances}) ->
    forM_ (take 1 [(left, right) | (index, left) <- zip [0 :: Int ..] classInstances, right <- drop (index + 1) classInstances, symbolModule left /= symbolModule right, sameInstance (K.Environment definitions) left right]) \(left, right) ->
      Left (CompileFailure CheckFailure Nothing Nothing ("bizens of class '" ++ symbolName family ++ "' from " ++ owner left ++ " and " ++ owner right ++ " have the same type"))
  pure (SourceProgram (K.Environment definitions) [] (Names (Map.unions [qualified, Map.map resolve alternatives, primitives]) instances) Set.empty (Names Map.empty instances) [] references [])
  where
    owner symbol = case symbolModule symbol of
      SourceModule path -> "'" ++ path ++ "'"
      _ -> "this module"
    -- cached modules may have been checked independently. shared identities
    -- must retain the same definitions, including transitive dependencies.
    mergeGlobals definitions (span, _, path, program) =
      let imported = globals (sourceEnvironment program)
          conflicts = Map.keys (Map.filter id (Map.intersectionWith (/=) definitions imported))
       in -- a family conflicteth with its eliminator; the family is named.
          case filter (isNothing . inducedFamily) conflicts ++ conflicts of
            symbol : _ -> Left (CompileFailure CheckFailure Nothing span ("conflicting definition of '" ++ symbolName symbol ++ "' in bring '" ++ path ++ "'"))
            [] -> pure (Map.union definitions imported)
    claimNamespace claimed (span, space, path, _) = case Map.lookup space claimed of
      Just other | path /= other -> Left (CompileFailure CheckFailure Nothing span ("bring namespace '" ++ space ++ "' nameth both '" ++ other ++ "' and '" ++ path ++ "'"))
      _ -> pure (Map.insert space path claimed)

-- declarations are checked in dependency order, so source order doth not
-- matter. a declaration followeth the declarations whose names it useth, and a
-- let or bizen that useth a class member, or an imported name whose type
-- requireth the class, followeth the module's bizens of that class. a cycle of types is
-- checked together; every other cycle is rejected.
-- among ready groups, source order winneth, as it doth within each group.
data DeclarationGroup = DeclarationGroup
  { groupIndices :: Set.Set Int,
    groupEntries :: [(Maybe SourceSpan, Declaration)],
    groupRequired :: Set.Set Int,
    groupFailure :: Maybe CompileFailure
  }

orderDeclarations :: SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Either CompileFailure [[(Maybe SourceSpan, Declaration)]]
orderDeclarations program declarations = declarationGroups program declarations >>= traverse (\DeclarationGroup {..} -> maybe (Right groupEntries) Left groupFailure)

declarationGroups :: SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Either CompileFailure [DeclarationGroup]
declarationGroups program located = go (sortOn (Set.findMin . groupIndices) (map group components))
  where
    instances = nameClasses (globalNames program)
    importedMembers = Map.fromList [(member, symbolName family) | (family, ClassInfo {classMembers}) <- Map.toList instances, member <- classMembers]
    importedParents = Map.fromList [(symbolName family, map symbolName classParents) | (family, ClassInfo {classParents}) <- Map.toList instances]
    declarations = map snd located
    -- each declaration's hard and soft dependencies are computed once and
    -- carried with it.
    scheduled = [(index, entry, without index hard, without index soft) | (index, entry@(_, declaration)) <- zip [0 :: Int ..] located, let (hard, soft) = dependencies index declaration]
    without index = Set.delete index . Set.fromList
    components = concatMap relax (strongly scheduled)
    strongly nodes = stronglyConnComp [(node, index, Set.toList (hard <> soft)) | node@(index, _, hard, soft) <- nodes]
    -- a cycle that a soft wait closeth is ordered again by its hard edges and
    -- the soft edges that leave it: its members meet each such use with their
    -- own requirements, so they need not wait for the module's bizens.
    relax component = case component of
      CyclicSCC nodes
        | not (all (inductive . entryOf) nodes),
          let inside = Set.fromList [index | (index, _, _, _) <- nodes],
          relaxed <- strongly [(index, entry, hard, soft `Set.difference` inside) | (index, entry, hard, soft) <- nodes],
          length relaxed > 1 ->
            relaxed
      _ -> [component]
    entryOf (_, entry, _, _) = entry
    inductive (_, declaration) = case unshown declaration of InductiveDeclaration {} -> True; _ -> False
    group component =
      let nodes = sortOn (\(index, _, _, _) -> index) (flattenSCC component)
          indices = Set.fromList [index | (index, _, _, _) <- nodes]
          entries = map entryOf nodes
          required = Set.unions [hard <> soft | (_, _, hard, soft) <- nodes] `Set.difference` indices
          failure = case component of
            CyclicSCC _ | not (all inductive entries) -> Just (cycleError entries)
            _ -> Nothing
       in DeclarationGroup indices entries required failure
    go [] = pure []
    go remaining =
      let pending = Set.unions (map groupIndices remaining)
          ready = Set.disjoint pending . groupRequired
       in case break ready remaining of
            (before, found : after) -> (found :) <$> go (before ++ after)
            (_, []) -> Left (cycleError (concatMap groupEntries remaining))
    cycleError entries =
      CompileFailure CheckFailure Nothing (fst =<< listToMaybe entries) ("declaration cycle: " ++ intercalate " -> " (map (label . snd) entries))
    label declaration = case defines declaration of
      name : _ -> name
      [] -> maybe "declaration" ("bizen " ++) (instanceClass declaration)
    indexed = zip [0 ..] declarations
    -- a module's own let of a member's name shadoweth the member.
    shadowed = Set.fromList [declarationName | Declaration {declarationName} <- map unshown declarations]
    definers = Map.fromList [(name, index) | (index, declaration) <- indexed, name <- defines declaration]
    members = Map.union (Map.fromList [(member, classDeclarationName) | ClassDeclaration classDeclarationName _ classDeclarationMembers <- map unshown declarations, ClassMember member _ <- classDeclarationMembers]) importedMembers
    instancesOf = Map.fromListWith (++) [(className, [index]) | (index, declaration@BizenDeclaration {}) <- indexed, Just className <- [instanceClass declaration]]
    -- class laws and member types use the class's own dictionary, and data
    -- declarations use no dictionary, so only lets and bizens wait for bizens.
    -- a member's use, or a use of an imported name that requireth a class, waiteth for
    -- the module's bizens of that class, except a bizen that itself needeth
    -- this declaration by name, as a helper proof used by its own class's
    -- bizen; that bizen cannot be the one it useth.
    -- waiting for bizens is soft: it giveth way inside a cycle it closeth.
    dependencies index declaration =
      let usesInstances = case unshown declaration of
            Declaration {} -> True
            BizenDeclaration {} -> True
            _ -> False
       in ( nameDependencies Map.! index
              ++ [instanceIndex | Just className <- [instanceClass declaration], ancestor <- ancestors className, instanceIndex <- Map.findWithDefault [] ancestor instancesOf],
            [instanceIndex | usesInstances, name <- mentioned declaration, className <- classesUsedBy name, instanceIndex <- Map.findWithDefault [] className instancesOf, not (reaches instanceIndex index)]
          )
    classesUsedBy name =
      [className | Set.notMember name shadowed, Just className <- [Map.lookup name members]] ++ requiredClasses name
    -- the classes of an imported global's anonymous implicit slots, from its
    -- checked type. a local name is already ordered by each use, and its
    -- requirements are often met by the caller's own requirements.
    requiredClasses name
      | Map.member name definers = []
      | otherwise = case bindingSymbol =<< lookupName name (globalNames program) of
          Just symbol | Just Definition {definitionType} <- Map.lookup symbol (globals (programEnvironment program)) -> checkedRequirements definitionType
          _ -> []
    checkedRequirements = \case
      Pi Implicit domain codomain -> [symbolName family | Just family <- [checkedHead domain], Map.member family instances] ++ checkedRequirements codomain
      Pi _ _ codomain -> checkedRequirements codomain
      _ -> []
    checkedHead = \case
      Apply _ function _ -> checkedHead function
      Global symbol _ -> Just symbol
      _ -> Nothing
    nameDependencies = Map.fromList [(index, [definer | name <- mentioned declaration, Just definer <- [Map.lookup name definers]]) | (index, declaration) <- indexed]
    -- whether one declaration needeth another through names alone.
    reaches from target = go' Set.empty [from]
      where
        go' _ [] = False
        go' seen (current : rest)
          | current == target = True
          | current `Set.member` seen = go' seen rest
          | otherwise = go' (Set.insert current seen) (Map.findWithDefault [] current nameDependencies ++ rest)
    -- a bizen's dictionary needeth bizens of every ancestor class.
    parentsOf = Map.union (Map.fromList [(classDeclarationName, [name | Parameter {parameterName = Nothing, parameterType} <- classDeclarationParameters, Just name <- [lastSegment <$> headName parameterType]]) | ClassDeclaration classDeclarationName classDeclarationParameters _ <- map unshown declarations]) importedParents
    ancestors className = go' Set.empty (Map.findWithDefault [] className parentsOf)
      where
        go' _ [] = []
        go' seen (parent : rest)
          | parent `Set.member` seen = go' seen rest
          | otherwise = parent : go' (Set.insert parent seen) (Map.findWithDefault [] parent parentsOf ++ rest)
    headName = \case
      Application (Name name) _ -> Just name
      Name name -> Just name
      _ -> Nothing
    constructors = Set.fromList [constructorName constructor | InductiveDeclaration {inductiveConstructors} <- map unshown declarations, constructor <- inductiveConstructors]
    mentioned declaration = Set.toList . Set.unions . map (freeNames (`Set.member` constructors) Set.empty) $ case unshown declaration of
      Declaration {..} -> maybe [] pure declarationAnnotation ++ [declarationBody]
      HostDeclaration {hostAnnotation, hostModel} -> hostAnnotation : maybe [] pure hostModel
      AssumptionDeclaration {assumptionAnnotation} -> [assumptionAnnotation]
      InductiveDeclaration {..} -> inductiveSignature : map constructorAnnotation inductiveConstructors
      ClassDeclaration {..} -> map parameterType classDeclarationParameters ++ [ty | ClassMember _ ty <- classDeclarationMembers]
      BizenDeclaration {..} -> bizenType : concat [maybe [] pure declarationAnnotation ++ [declarationBody] | Declaration {..} <- bizenMembers]
      _ -> []
    instanceClass BizenDeclaration {bizenType} = lastSegment <$> written bizenType
      where
        written = \case
          Product _ result -> written result
          other -> headName other
    instanceClass _ = Nothing
    lastSegment = Name.lastQualifiedSegment

defines :: Declaration -> [String]
defines declaration = case unshown declaration of
  Declaration {declarationName} -> [declarationName]
  HostDeclaration {hostName} -> [hostName]
  AssumptionDeclaration {assumptionName} -> [assumptionName]
  InductiveDeclaration {inductiveName, inductiveConstructors} -> inductiveName : map constructorName inductiveConstructors
  ClassDeclaration {classDeclarationName, classDeclarationMembers} -> classDeclarationName : (classDeclarationName ++ "_make") : [member | ClassMember member _ <- classDeclarationMembers]
  _ -> []
