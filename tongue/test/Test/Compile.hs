-- source text compiled as the library compileth snapshots. the string forms
-- keep only a failure's text.
module Test.Compile
  ( compileSource,
    compileProject,
    compileProjectWith,
    compileProjectDetailed,
    compileYieldWith,
    bookhoardSources,
    loadBookhoard,
    shareBookhoard,
    checkBookhoardModule,
  )
where

import Control.Exception (evaluate)
import Data.Bifunctor (first)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.Map.Strict qualified as Map
import System.Directory (removePathForcibly)
import System.Environment (lookupEnv)
import System.IO.Unsafe (unsafePerformIO)
import Tung (readLibraryImports)
import Tung.Dependent (Inferred, ModuleId)
import Tung.Dependent.Source (CompileFailure (..), SourceProgram, SourceSnapshot, cacheKeys, compileImports, compileSnapshot, compilerBuild, loadInterfaces, saveInterfaces, sourceSnapshot)

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

-- one bookhoard module checked from its source, its imports taken as given.
checkBookhoardModule :: Map.Map String SourceProgram -> String -> Either String SourceProgram
checkBookhoardModule imports path =
  let (_, snapshots, _) = bookhoard
   in maybe (Left ("library module was not loaded: " ++ path)) Right . Map.lookup path =<< first failureText (compileImports imports snapshots [path])

-- a group process beginneth with the interfaces its parent saved, if any.
{-# NOINLINE bookhoard #-}
bookhoard :: (Map.Map String String, Map.Map String SourceSnapshot, IORef (Map.Map String SourceProgram))
bookhoard = unsafePerformIO do
  sources <- readLibraryImports "." >>= either fail pure
  mapM_ (evaluate . length) (Map.elems sources)
  let snapshots = Map.map sourceSnapshot sources
  initial <-
    lookupEnv sharedVariable >>= \case
      Just directory -> compilerBuild >>= loadInterfaces directory snapshots . (`cacheKeys` snapshots)
      Nothing -> pure Map.empty
  cache <- newIORef initial
  pure (sources, snapshots, cache)

-- the parent test process checketh all of bookhoard once and saveth its
-- interfaces in a fresh directory, which it nameth to its group processes.
-- a failure saveth nothing, so each group checketh and reporteth it again.
shareBookhoard :: IO (String, FilePath)
shareBookhoard = do
  let directory = "dist-newstyle/test-interfaces"
      (_, snapshots, _) = bookhoard
  removePathForcibly directory
  build <- compilerBuild
  either (const (pure ())) (saveInterfaces directory (cacheKeys build snapshots)) (compileImports Map.empty snapshots (Map.keys snapshots))
  pure (sharedVariable, directory)

sharedVariable :: String
sharedVariable = "TUNG_TEST_INTERFACES"
