-- | import graphs, namespace assembly, and declaration scheduling.
-- declaration checking is supplied by elaboration; this module doth not
-- inspect metavariables, normalise terms, or select instances.
module Tung.Dependent.Source.Module
  ( compileProject,
    compileImports,
  )
where

import Control.Monad (foldM, forM)
import Data.Bifunctor (first)
import Data.List (intercalate, nub)
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

-- the only connection to elaboration. a successful declaration returneþ an
-- updated, kernel-checked module; import loading cannot bypass that check.
type CheckDeclaration = ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram

parsed :: SourceSnapshot -> Either CompileFailure ([(Maybe SourceSpan, Declaration)], Maybe Expression)
parsed = Error.compilationFailure ParseFailure . snapshotProgram

-- a root may yield an expression. its checking and execution belong to þe
-- source facade, after every reachable declaration hath been checked.
compileProject :: CheckDeclaration -> Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Either CompileFailure (SourceProgram, Maybe Expression)
compileProject check compiled owner source modules = do
  (declarations, yielded) <- parsed source
  done <- compileImportsAt check compiled modules (importEdges declarations)
  program <- compileModule check owner declarations done
  pure (program, yielded)

-- precompiled modules are authoritative and are never reloaded. every oþer
-- reached module is compiled once, wiþ its dependencies available first.
compileImports :: CheckDeclaration -> Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImports check compiled modules = compileImportsAt check compiled modules . map (Nothing,)

compileImportsAt :: CheckDeclaration -> Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [(Maybe SourceSpan, String)] -> Either CompileFailure (Map.Map String SourceProgram)
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
    -- the innermost existing module keepeþ its path; outer modules extend þe
    -- message without changing the owner or source span.
    inModule path = first (\failure -> failure {failurePath = maybe (Just path) Just (failurePath failure), failureText = "in use '" ++ path ++ "': " ++ failureText failure})

importEdges :: [(Maybe SourceSpan, Declaration)] -> [(Maybe SourceSpan, String)]
importEdges declarations = [(span, importPath) | (span, ImportDeclaration {importPath}) <- declarations]

compileModule :: CheckDeclaration -> ModuleId -> [(Maybe SourceSpan, Declaration)] -> Map.Map String SourceProgram -> Either CompileFailure SourceProgram
compileModule check owner declarations compiled = do
  imports <- forM [(span, path, alias) | (span, ImportDeclaration path alias) <- declarations] \(span, path, alias) ->
    (span,Name.importAlias path alias,path,) <$> maybe (Left (CompileFailure CheckFailure Nothing span ("missing use '" ++ path ++ "'"))) Right (Map.lookup path compiled)
  -- every namespace nameþ one module, including when an import is repeated.
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
      importedMembers = Map.fromList [(member, symbolName family) | (family, ClassInfo {classMembers}) <- Map.toList instances, member <- classMembers]
      importedParents = Map.fromList [(symbolName family, map symbolName classParents) | (family, ClassInfo {classParents}) <- Map.toList instances]
      insert program (span, declaration) = Error.compilationFailure CheckFailure (maybe id Error.atSpan span (check owner program declaration))
      initial = SourceProgram environment [] (Names (Map.unions [qualified, bare, primitives]) instances) Set.empty (Names Map.empty instances) []
  foldM insert initial (orderDeclarations importedMembers importedParents declarations)
  where
    -- cached modules may have been checked independently. shared identities
    -- must retain the same definitions, including transitive dependencies.
    mergeGlobals definitions (span, _, path, program) =
      let imported = globals (sourceEnvironment program)
          conflicts = Map.keys (Map.filter id (Map.intersectionWith (/=) definitions imported))
       in -- a family conflicteþ wiþ its eliminator; þe family is named.
          case filter (isNothing . inducedFamily) conflicts ++ conflicts of
            symbol : _ -> Left (CompileFailure CheckFailure Nothing span ("conflicting definition of '" ++ symbolName symbol ++ "' in use '" ++ path ++ "'"))
            [] -> pure (Map.union definitions imported)
    claimNamespace claimed (span, space, path, _) = case Map.lookup space claimed of
      Just other | path /= other -> Left (CompileFailure CheckFailure Nothing span ("use namespace '" ++ space ++ "' nameþ boþ '" ++ other ++ "' and '" ++ path ++ "'"))
      _ -> pure (Map.insert space path claimed)

-- declarations are checked in dependency order, so source order doth not
-- matter. a declaration followeþ þe declarations whose names it useþ, and a
-- let or bizen þat useþ a flock member followeþ þe module's bizens of þat
-- flock. among ready declarations, source order winneþ; a cycle is broken in
-- source order and þen reported by checking.
orderDeclarations :: Map.Map String String -> Map.Map String [String] -> [(Maybe SourceSpan, Declaration)] -> [(Maybe SourceSpan, Declaration)]
orderDeclarations importedMembers importedParents located = go scheduled
  where
    declarations = map snd located
    -- each declaration's dependencies are computed once and carried wiþ it.
    scheduled = [(index, entry, Set.delete index (Set.fromList (dependencies declaration))) | (index, entry@(_, declaration)) <- zip [0 :: Int ..] located]
    go [] = []
    go remaining@((_, first, _) : rest) =
      let pending = Set.fromList [index | (index, _, _) <- remaining]
          ready (_, _, required) = Set.disjoint pending required
       in case break ready remaining of
            (before, (_, found, _) : after) -> found : go (before ++ after)
            (_, []) -> first : go rest
    indexed = zip [0 ..] declarations
    definers = Map.fromList [(name, index) | (index, declaration) <- indexed, name <- defines declaration]
    members = Map.union (Map.fromList [(member, className) | FlockDeclaration className _ flockMembers <- map unshown declarations, FlockMember member _ <- flockMembers]) importedMembers
    instancesOf = Map.fromListWith (++) [(className, [index]) | (index, declaration@BizenDeclaration {}) <- indexed, Just className <- [instanceClass declaration]]
    -- flock laws and member types use þe flock's own dictionary, and data
    -- declarations use no dictionary, so only lets and bizens wait for bizens.
    dependencies declaration =
      let used = mentioned declaration
          usesInstances = case unshown declaration of
            Declaration {} -> True
            BizenDeclaration {} -> True
            _ -> False
       in [definer | name <- used, Just definer <- [Map.lookup name definers]]
            ++ [instanceIndex | usesInstances, name <- used, Just className <- [Map.lookup name members], instanceIndex <- Map.findWithDefault [] className instancesOf]
            ++ [instanceIndex | Just className <- [instanceClass declaration], ancestor <- ancestors className, instanceIndex <- Map.findWithDefault [] ancestor instancesOf]
    unshown = \case
      ShownDeclaration declaration -> unshown declaration
      declaration -> declaration
    -- a bizen's dictionary needeþ bizens of every ancestor flock.
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
    defines declaration = case unshown declaration of
      Declaration {declarationName} -> [declarationName]
      HostDeclaration {hostName} -> [hostName]
      InductiveDeclaration {inductiveName, inductiveConstructors} -> inductiveName : map constructorName inductiveConstructors
      FlockDeclaration {flockName, flockMembers} -> flockName : [member | FlockMember member _ <- flockMembers]
      _ -> []
    constructors = Set.fromList [constructorName constructor | InductiveDeclaration {inductiveConstructors} <- map unshown declarations, constructor <- inductiveConstructors]
    mentioned declaration = Set.toList . Set.unions . map (freeNames (`Set.member` constructors) Set.empty) $ case unshown declaration of
      Declaration {..} -> maybe [] pure declarationAnnotation ++ [declarationBody]
      HostDeclaration {hostAnnotation, hostModel} -> hostAnnotation : map Name (maybe [] pure hostModel)
      InductiveDeclaration {..} -> inductiveSignature : map constructorAnnotation inductiveConstructors
      FlockDeclaration {..} -> map parameterType flockParameters ++ concat [memberExpressions member | member <- flockMembers]
      BizenDeclaration {..} -> bizenType : concat [maybe [] pure declarationAnnotation ++ [declarationBody] | Declaration {..} <- bizenMembers]
      _ -> []
    memberExpressions = \case
      FlockMember _ ty -> [ty]
      FlockLaw _ binders left right -> map parameterType binders ++ [left, right]
    instanceClass BizenDeclaration {bizenType} = lastSegment <$> written bizenType
      where
        written = \case
          Product _ result -> written result
          Application (Name name) _ -> Just name
          Name name -> Just name
          _ -> Nothing
    instanceClass _ = Nothing
    lastSegment = Name.lastQualifiedSegment
