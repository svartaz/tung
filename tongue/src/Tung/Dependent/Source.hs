-- | the dependent source boundary useth one syntax and namespace for types and
-- values. only closed, kernel-checked definitions enter a source program.
module Tung.Dependent.Source
  ( SourceProgram,
    sourceEnvironment,
    sourceDefinitions,
    sourceGlobal,
    compileSnapshot,
    compileImports,
    recoverSnapshotHoles,
    cacheKeys,
    compilerBuild,
    loadInterfaces,
    saveInterfaces,
    CompileFailure (..),
    FailureKind (..),
    SourceSnapshot,
    sourceSnapshot,
    recoverSnapshot,
    snapshotText,
    snapshotImportPaths,
    typeOfName,
    sorryAssumptions,
    orsendAssumptions,
    DependencyKind (..),
    ProofDependency (..),
    ProofAudit,
    auditName,
    auditType,
    auditDependencies,
    auditProof,
    verifyProof,
    Hole (..),
    sourceHoles,
    sourceExports,
    inferSourceExpression,
    normaliseSourceExpression,
    Expression,
    Parameter (..),
    Binder (..),
    Argument (..),
    Declaration (..),
    ConstructorDeclaration (..),
    Row (..),
    parseSource,
    parseProgram,
    sketch,
    parseExpression,
  )
where

import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Cache (cacheKeys, compilerBuild, loadInterfaces, saveInterfaces)
import Tung.Dependent.Source.Declaration (insertDeclarations, recoverDeclarations)
import Tung.Dependent.Source.Elaborate (elaborateHoles, elaborateHolesReport)
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Expression (inferExpression)
import Tung.Dependent.Source.Module qualified as Modules
import Tung.Dependent.Source.Parse (SourceSnapshot, parseExpression, parseProgram, parseSource, recoverSnapshot, snapshotImportPaths, snapshotText, sourceSnapshot)
import Tung.Dependent.Source.Proof
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Identity (ModuleId (..))
import Tung.Token (SourceFailure (..), SourceSpan (..))

-- a root module and the modules it useth, keyed by `use` path. each is checked
-- once, in dependency order, and modules already compiled are reused
-- unchanged; a cycle is an error. a root that endeth in `yield` returneth the
-- yielded expression, checked against the finished module.
compileSnapshot :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Either CompileFailure (SourceProgram, Maybe K.Inferred)
compileSnapshot compiled owner source modules = do
  (program, yielded) <- Modules.compileProject insertDeclarations compiled owner source modules
  checked <- traverse (Error.compilationFailure CheckFailure . inferInHoles program) yielded
  let holes = maybe [] snd checked
  pure (program {programHoles = reverse holes ++ programHoles program}, fst <$> checked)

-- the named modules and everything they use.
compileImports :: Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImports = Modules.compileImports insertDeclarations

-- best-effort goals for diagnostics. imports still check in full; failed local
-- groups are never inserted, and no partial program escapeth this function.
-- syntax recovery only retains complete declarations at safe boundaries.
recoverSnapshotHoles :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> [Hole]
recoverSnapshotHoles compiled owner source modules =
  case Modules.recoverModule recoverDeclarations owner declarations reached of
    Nothing -> []
    Just (program, holes) -> sortOn (fmap spanStart . holeSpan) (holes ++ yieldedHoles program)
  where
    (declarations, yielded, _) = recoverSnapshot source
    reached = foldl load compiled [path | (_, ImportDeclaration path _) <- declarations]
    load done path = either (const done) id (compileImports done modules [path])
    yieldedHoles program@SourceProgram {..} = maybe [] (\expression -> snd (elaborateHolesReport program ((\(term, ty) -> (term, ty, ())) <$> inferExpression programEnvironment globalNames emptyScope expression))) yielded

inferSourceExpression :: SourceProgram -> String -> Either String K.Inferred
inferSourceExpression program source = parseExpression source >>= Error.toString . inferIn program

inferIn :: SourceProgram -> Expression -> Either SourceFailure K.Inferred
inferIn program expression = fst <$> inferInHoles program expression

inferInHoles :: SourceProgram -> Expression -> Either SourceFailure (K.Inferred, [Hole])
inferInHoles program@SourceProgram {..} expression = do
  (result, (), holes, _) <- elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> inferExpression programEnvironment globalNames emptyScope expression)
  Error.fromString (K.validate programEnvironment result)
  pure (result, holes)

normaliseSourceExpression :: SourceProgram -> String -> Either String Term
normaliseSourceExpression program@SourceProgram {..} source = do
  result <- inferSourceExpression program source
  -- source inference rechecketh the generalised term before raw NBE can see it.
  N.normalise (globals programEnvironment) 0 (K.inferredTerm result)
