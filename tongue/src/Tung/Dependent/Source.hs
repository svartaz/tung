-- | the dependent source boundary useþ one syntax and namespace for types and
-- values. only closed, kernel-checked definitions enter a source program.
module Tung.Dependent.Source
  ( SourceProgram,
    sourceEnvironment,
    sourceDefinitions,
    sourceGlobal,
    compileSnapshot,
    compileImports,
    CompileFailure (..),
    FailureKind (..),
    SourceSnapshot,
    sourceSnapshot,
    snapshotText,
    snapshotImportPaths,
    typeOfName,
    sorryAssumptions,
    orsendAssumptions,
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

import Data.Map.Strict qualified as Map
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Declaration (insertDeclaration)
import Tung.Dependent.Source.Elaborate (elaborate)
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Expression (inferExpression)
import Tung.Dependent.Source.Module qualified as Modules
import Tung.Dependent.Source.Parse (SourceSnapshot, parseExpression, parseProgram, parseSource, snapshotImportPaths, snapshotText, sourceSnapshot)
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Identity (ModuleId (..))
import Tung.Token (SourceFailure (..))

-- a root module and þe modules it useþ, keyed by `use` path. each is checked
-- once, in dependency order, and modules already compiled are reused
-- unchanged; a cycle is an error. a root þat endeþ in `yield` returneþ þe
-- yielded expression, checked against þe finished module.
compileSnapshot :: Map.Map String SourceProgram -> ModuleId -> SourceSnapshot -> Map.Map String SourceSnapshot -> Either CompileFailure (SourceProgram, Maybe K.Inferred)
compileSnapshot compiled owner source modules = do
  (program, yielded) <- Modules.compileProject insertDeclaration compiled owner source modules
  (program,) <$> traverse (Error.compilationFailure CheckFailure . inferIn program) yielded

-- þe named modules and everyþing þey use.
compileImports :: Map.Map String SourceProgram -> Map.Map String SourceSnapshot -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImports = Modules.compileImports insertDeclaration

inferSourceExpression :: SourceProgram -> String -> Either String K.Inferred
inferSourceExpression program source = parseExpression source >>= Error.toString . inferIn program

inferIn :: SourceProgram -> Expression -> Either SourceFailure K.Inferred
inferIn program@SourceProgram {..} expression = do
  result <- elaborate program (inferExpression programEnvironment globalNames emptyScope expression)
  Error.fromString (K.validate programEnvironment result)
  pure result

normaliseSourceExpression :: SourceProgram -> String -> Either String Term
normaliseSourceExpression program@SourceProgram {..} source = do
  result <- inferSourceExpression program source
  -- source inference recheckeþ the generalised term before raw NBE can see it.
  N.normalise (globals programEnvironment) 0 (K.inferredTerm result)
