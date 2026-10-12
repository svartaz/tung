-- source text compiled as the library compileth snapshots. the string forms
-- keep only a failure's text.
module Test.Compile
  ( compileSource,
    compileProject,
    compileProjectWith,
    compileProjectDetailed,
    compileYieldWith,
    compileModules,
    bookhoardSources,
    loadBookhoard,
  )
where

import Control.Exception (evaluate)
import Data.Bifunctor (first)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Map.Strict qualified as Map
import System.IO.Unsafe (unsafePerformIO)
import Tung (readLibraryImports)
import Tung.Dependent (Inferred, ModuleId)
import Tung.Dependent.Source (CompileFailure (..), SourceProgram, SourceSnapshot, compileImports, compileSnapshot, sourceSnapshot)

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

-- each test process readeth one immutable source snapshot. fixture overrides
-- bypass this cache, including every transitive dependant of a changed source.
bookhoardSources :: Map.Map String String
bookhoardSources = let (sources, _, _) = bookhoard in sources

loadBookhoard :: [String] -> IO (Either String (Map.Map String SourceProgram))
loadBookhoard paths =
  let (_, snapshots, cache) = bookhoard
   in atomicModifyIORef' cache \checked -> case compileImports checked snapshots paths of
        Left failure -> (checked, Left (failureText failure))
        Right compiled -> (compiled, Right compiled)

{-# NOINLINE bookhoard #-}
bookhoard :: (Map.Map String String, Map.Map String SourceSnapshot, IORef (Map.Map String SourceProgram))
bookhoard = unsafePerformIO do
  sources <- readLibraryImports "." >>= either fail pure
  mapM_ (evaluate . length) (Map.elems sources)
  cache <- newIORef Map.empty
  pure (sources, Map.map sourceSnapshot sources, cache)
