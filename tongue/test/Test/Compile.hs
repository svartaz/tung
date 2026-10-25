-- source text compiled as the library compileth snapshots. the string forms
-- keep only a failure's text.
module Test.Compile
  ( compileSource,
    compileProject,
    compileProjectWith,
    compileProjectDetailed,
    compileYieldWith,
    standardSources,
    loadStandard,
    shareStandard,
    checkStandardModule,
  )
where

import Control.Exception (evaluate)
import Data.Bifunctor (first)
import Data.Bits (xor)
import Data.Char (ord)
import Data.IORef (IORef, atomicModifyIORef', newIORef)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, listDirectory, removeFile)
import System.Environment (lookupEnv)
import System.FilePath (takeBaseName, takeExtension, (</>))
import System.IO.Unsafe (unsafePerformIO)
import Tung (readLibraryImports)
import Tung.Dependent (Inferred, ModuleId)
import Tung.Dependent.Source (CompileFailure (..), SourceProgram, SourceSnapshot, cacheKeys, compileImports, compileSnapshot, loadInterfaces, saveInterfaces, sourceSnapshot)

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
standardSources :: Map.Map String String
standardSources = let (sources, _, _) = standard in sources

loadStandard :: [String] -> IO (Either String (Map.Map String SourceProgram))
loadStandard paths =
  let (_, snapshots, cache) = standard
   in atomicModifyIORef' cache \checked -> case compileImports checked snapshots paths of
        Left failure -> (checked, Left (failureText failure))
        Right compiled -> (compiled, Right compiled)

-- one library module checked from its source, its imports taken as given.
checkStandardModule :: Map.Map String SourceProgram -> String -> Either String SourceProgram
checkStandardModule imports path =
  let (_, snapshots, _) = standard
   in maybe (Left ("library module was not loaded: " ++ path)) Right . Map.lookup path =<< first failureText (compileImports imports snapshots [path])

-- a group process beginneth with the interfaces its parent saved, if any.
{-# NOINLINE standard #-}
standard :: (Map.Map String String, Map.Map String SourceSnapshot, IORef (Map.Map String SourceProgram))
standard = unsafePerformIO do
  sources <- readLibraryImports "." >>= either fail pure
  mapM_ (evaluate . length) (Map.elems sources)
  let snapshots = Map.map sourceSnapshot sources
  initial <-
    lookupEnv sharedVariable >>= \case
      Just directory -> libraryBuild >>= loadInterfaces directory snapshots . (`cacheKeys` snapshots)
      Nothing -> pure Map.empty
  cache <- newIORef initial
  pure (sources, snapshots, cache)

-- the parent test process checketh the library once and saveth its interfaces
-- in a directory it nameth to its group processes. interfaces an earlier run
-- saved for the same sources are reused, and stale ones removed. a failure
-- saveth nothing, so each group checketh and reporteth it again.
shareStandard :: IO (String, FilePath)
shareStandard = do
  let directory = "dist-newstyle/test-interfaces"
      (_, snapshots, _) = standard
  keys <- (`cacheKeys` snapshots) <$> libraryBuild
  cached <- loadInterfaces directory snapshots keys
  either (const (pure ())) (saveInterfaces directory keys . (`Map.difference` cached)) (compileImports cached snapshots (Map.keys snapshots))
  createDirectoryIfMissing True directory
  stale <- filter ((`notElem` Map.elems keys) . takeBaseName) <$> listDirectory directory
  mapM_ (removeFile . (directory </>)) stale
  pure (sharedVariable, directory)

-- checking dependeth only on the compiler library's sources, so interfaces
-- outlive a rebuild that changed only the tests.
libraryBuild :: IO String
libraryBuild = show . foldl' (\hash character -> (hash `xor` ord character) * 16777619) (2166136261 :: Int) . concat <$> (traverse readFile . sort =<< sources "src")
  where
    sources directory = do
      entries <- map (directory </>) <$> listDirectory directory
      concat <$> traverse (\entry -> doesDirectoryExist entry >>= \nested -> if nested then sources entry else pure [entry | takeExtension entry == ".hs"]) entries

sharedVariable :: String
sharedVariable = "TUNG_TEST_INTERFACES"
