-- source text compiled as the library compileth snapshots. the string forms
-- keep only a failure's text.
module Test.Compile
  ( compileSource,
    compileProject,
    compileProjectWith,
    compileProjectDetailed,
    compileYieldWith,
    compileModules,
  )
where

import Data.Bifunctor (first)
import Data.Map.Strict qualified as Map
import Tung.Dependent (Inferred, ModuleId)
import Tung.Dependent.Source (CompileFailure (..), SourceProgram, compileImports, compileSnapshot, sourceSnapshot)

compileSource :: ModuleId -> String -> Either String SourceProgram
compileSource owner source = compileProject owner source Map.empty

compileProject :: ModuleId -> String -> Map.Map String String -> Either String SourceProgram
compileProject = compileProjectWith Map.empty

compileProjectWith :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either String SourceProgram
compileProjectWith compiled owner source = first failureText . compileProjectDetailed compiled owner source

compileProjectDetailed :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either CompileFailure SourceProgram
compileProjectDetailed compiled owner source modules = fst <$> compileSnapshot compiled owner (sourceSnapshot source) (Map.map sourceSnapshot modules)

compileYieldWith :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either String (SourceProgram, Maybe Inferred)
compileYieldWith compiled owner source modules = first failureText (compileSnapshot compiled owner (sourceSnapshot source) (Map.map sourceSnapshot modules))

compileModules :: Map.Map String String -> [String] -> Either String (Map.Map String SourceProgram)
compileModules modules = first failureText . compileImports Map.empty (Map.map sourceSnapshot modules)
