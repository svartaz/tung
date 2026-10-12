-- | import graphs, namespace assembly, and declaration scheduling.
-- declaration checking is supplied by elaboration; this module doth not
-- inspect metavariables, normalise terms, or select instances.
module Tung.Dependent.Source.Module
  ( compileProject,
    compileImports,
    recoverModule,
  )
where

import Control.Monad (foldM, forM)
import Data.Bifunctor (first)
import Data.Graph (SCC (..), flattenSCC, stronglyConnComp)
import Data.List (intercalate, nub, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Parse (SourceSnapshot (..))
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax (Definition (..))
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
      | path `elem` stack = Left (CompileFailure CheckFailure Nothing span ("use cycle: " ++ intercalate " -> " (reverse (path : stack))))
      | otherwise = do
          -- an absent source and a cycle are faults in the importing module,
          -- so neither may acquire the missing or repeated module's path.
          imported <- maybe (Left (CompileFailure CheckFailure Nothing span ("missing use '" ++ path ++ "'"))) Right (Map.lookup path modules)
          inModule path do
            (declarations, _) <- parsed imported
            done' <- foldM (compileImport (path : stack)) done (importEdges declarations)
            program <- compileModule check (SourceModule path) declarations done'
            pure (Map.insert path program done')
    -- the innermost existing module keepeth its path; outer modules extend the
    -- message without changing the owner or source span.
    inModule path = first (\failure -> failure {failurePath = maybe (Just path) Just (failurePath failure), failureText = "in use '" ++ path ++ "': " ++ failureText failure})

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
recoverModule :: (ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> (Either SourceFailure SourceProgram, [Hole])) -> ModuleId -> [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Maybe (SourceProgram, [Hole])
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
  pure (program, concat (reverse chunks))

moduleEnvironment :: [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Either CompileFailure SourceProgram
moduleEnvironment declarations compiled = do
  imports <- forM [(span, path, alias) | (span, ImportDeclaration path alias) <- declarations] \(span, path, alias) ->
    (span,Name.importAlias path alias,path,) <$> maybe (Left (CompileFailure CheckFailure Nothing span ("missing use '" ++ path ++ "'"))) Right (Map.lookup path compiled)
  -- every namespace nameth one module, including when an import is repeated.
  foldM claimNamespace Map.empty imports
  definitions <- foldM mergeGlobals H.primitiveDefinitions imports
  let environment = K.Environment definitions
      qualified = Map.fromList [(space ++ "~" ++ name, binding) | (_, space, _, program) <- imports, (name, binding) <- Map.toList (nameTable (sourceExports program))]
      -- provenance is the visible import namespace, not the defining module.
      -- re-exports preserve identities but may arrive under different aliases.
      alternatives = Map.fromListWith (++) [(name, [(binding, space)]) | (_, space, _, program) <- imports, (name, binding) <- Map.toList (nameTable (sourceExports program))]
      bare = Map.map resolve alternatives
      resolve bindings = case nub (map fst bindings) of
        [binding] -> binding
        _ -> AmbiguousName (nub (map snd bindings))
      -- instances are global: every imported registry is merged.
      instances = Map.unionsWith mergeClass [nameClasses (sourceExports program) | (_, _, _, program) <- imports]
      -- imported and local names shadow primitive types.
      primitives = Map.fromList [(symbolName symbol, FreshName symbol (definitionUniverses definition)) | (symbol, definition) <- Map.toList H.primitiveDefinitions, symbol /= H.sorrySymbol, isNothing (inducedFamily symbol)]
      references = Map.unionsWith Set.union [programReferences program | (_, _, _, program) <- imports]
      initial = SourceProgram environment [] (Names (Map.unions [qualified, bare, primitives]) instances) Set.empty (Names Map.empty instances) [] references
  pure initial
  where
    -- cached modules may have been checked independently. shared identities
    -- must retain the same definitions, including transitive dependencies.
    mergeGlobals definitions (span, _, path, program) =
      let imported = globals (sourceEnvironment program)
          conflicts = Map.keys (Map.filter id (Map.intersectionWith (/=) definitions imported))
       in -- a family conflicteth with its eliminator; the family is named.
          case filter (isNothing . inducedFamily) conflicts ++ conflicts of
            symbol : _ -> Left (CompileFailure CheckFailure Nothing span ("conflicting definition of '" ++ symbolName symbol ++ "' in use '" ++ path ++ "'"))
            [] -> pure (Map.union definitions imported)
    claimNamespace claimed (span, space, path, _) = case Map.lookup space claimed of
      Just other | path /= other -> Left (CompileFailure CheckFailure Nothing span ("use namespace '" ++ space ++ "' nameth both '" ++ other ++ "' and '" ++ path ++ "'"))
      _ -> pure (Map.insert space path claimed)

-- declarations are checked in dependency order, so source order doth not
-- matter. a declaration followeth the declarations whose names it useth, and a
-- let or bizen that useth a flock member followeth the module's bizens of that
-- flock. a cycle of ilks is checked together; every other cycle is rejected.
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
    -- each declaration's dependencies are computed once and carried with it.
    scheduled = [(index, entry, Set.delete index (Set.fromList (dependencies index declaration))) | (index, entry@(_, declaration)) <- zip [0 :: Int ..] located]
    components = stronglyConnComp [(entry, index, Set.toList required) | entry@(index, _, required) <- scheduled]
    group component =
      let nodes = sortOn (\(index, _, _) -> index) (flattenSCC component)
          indices = Set.fromList [index | (index, _, _) <- nodes]
          entries = [entry | (_, entry, _) <- nodes]
          required = Set.unions [dependencies | (_, _, dependencies) <- nodes] `Set.difference` indices
          inductive (_, declaration) = case unshown declaration of InductiveDeclaration {} -> True; _ -> False
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
      CompileFailure CheckFailure Nothing (fst =<< firstEntry entries) ("declaration cycle: " ++ intercalate " -> " (map (label . snd) entries))
    firstEntry [] = Nothing
    firstEntry (entry : _) = Just entry
    label declaration = case defines declaration of
      name : _ -> name
      [] -> maybe "declaration" ("bizen " ++) (instanceClass declaration)
    indexed = zip [0 ..] declarations
    -- a module's own let of a member's name shadoweth the member.
    shadowed = Set.fromList [declarationName | Declaration {declarationName} <- map unshown declarations]
    definers = Map.fromList [(name, index) | (index, declaration) <- indexed, name <- defines declaration]
    members = Map.union (Map.fromList [(member, className) | FlockDeclaration className _ flockMembers <- map unshown declarations, FlockMember member _ <- flockMembers]) importedMembers
    instancesOf = Map.fromListWith (++) [(className, [index]) | (index, declaration@BizenDeclaration {}) <- indexed, Just className <- [instanceClass declaration]]
    -- flock laws and member types use the flock's own dictionary, and data
    -- declarations use no dictionary, so only lets and bizens wait for bizens.
    -- a member's use waiteth for the module's bizens of its flock, except a
    -- bizen that itself needeth this declaration by name, as a helper proof
    -- used by its own flock's bizen; that bizen cannot be the one it useth.
    dependencies index declaration =
      let used = mentioned declaration
          usesInstances = case unshown declaration of
            Declaration {} -> True
            BizenDeclaration {} -> True
            _ -> False
       in nameDependencies Map.! index
            ++ [instanceIndex | usesInstances, name <- used, Set.notMember name shadowed, Just className <- [Map.lookup name members], instanceIndex <- Map.findWithDefault [] className instancesOf, not (reaches instanceIndex index)]
            ++ [instanceIndex | Just className <- [instanceClass declaration], ancestor <- ancestors className, instanceIndex <- Map.findWithDefault [] ancestor instancesOf]
    nameDependencies = Map.fromList [(index, [definer | name <- mentioned declaration, Just definer <- [Map.lookup name definers]]) | (index, declaration) <- indexed]
    -- whether one declaration needeth another through names alone.
    reaches from target = go' Set.empty [from]
      where
        go' _ [] = False
        go' seen (current : rest)
          | current == target = True
          | current `Set.member` seen = go' seen rest
          | otherwise = go' (Set.insert current seen) (Map.findWithDefault [] current nameDependencies ++ rest)
    -- a bizen's dictionary needeth bizens of every ancestor flock.
    parentsOf = Map.union (Map.fromList [(className, [name | Parameter {parameterName = Nothing, parameterType} <- flockParameters, Just name <- [lastSegment <$> headName parameterType]]) | FlockDeclaration className flockParameters _ <- map unshown declarations]) importedParents
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
      FlockDeclaration {..} -> map parameterType flockParameters ++ [ty | FlockMember _ ty <- flockMembers]
      BizenDeclaration {..} -> bizenType : concat [maybe [] pure declarationAnnotation ++ [declarationBody] | Declaration {..} <- bizenMembers]
      _ -> []
    instanceClass BizenDeclaration {bizenType} = lastSegment <$> written bizenType
      where
        written = \case
          Product _ result -> written result
          Application (Name name) _ -> Just name
          Name name -> Just name
          _ -> Nothing
    instanceClass _ = Nothing
    lastSegment = Name.lastQualifiedSegment

unshown :: Declaration -> Declaration
unshown = \case
  ShownDeclaration declaration -> unshown declaration
  declaration -> declaration

defines :: Declaration -> [String]
defines declaration = case unshown declaration of
  Declaration {declarationName} -> [declarationName]
  HostDeclaration {hostName} -> [hostName]
  AssumptionDeclaration {assumptionName} -> [assumptionName]
  InductiveDeclaration {inductiveName, inductiveConstructors} -> inductiveName : map constructorName inductiveConstructors
  FlockDeclaration {flockName, flockMembers} -> flockName : (flockName ++ "_make") : [member | FlockMember member _ <- flockMembers]
  _ -> []
