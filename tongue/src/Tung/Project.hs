-- | filesystem project loading is kept outside parsing and import semantics.
-- the loader resolveþ relative imports into the flat source bundle consumed by the
-- checker, and rejecteþ path collisions instead of silently choosing one file.
module Tung.Project
  ( Project (..),
    loadProjectFile,
    loadProjectSource,
  )
where

import Control.Monad (filterM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.State.Strict (StateT, execStateT, gets, modify')
import Data.List (find, intercalate)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import System.Directory (canonicalizePath, doesFileExist, makeAbsolute)
import System.FilePath (normalise, takeDirectory, (</>))
import System.IO.Error (tryIOError)
import Tung.Dependent.Source (SourceSnapshot, snapshotImportPaths, snapshotText, sourceSnapshot)

-- a root source and every source it reacheþ, keyed by `use` path, wiþ þe
-- file each `use` path resolved to.
data Project = Project
  { projectPath :: FilePath,
    projectSource :: String,
    projectImports :: Map.Map String String,
    projectImportPaths :: Map.Map String FilePath,
    projectSnapshot :: SourceSnapshot,
    projectImportSnapshots :: Map.Map String SourceSnapshot
  }
  deriving stock (Eq, Show)

type Loaded = Map.Map String (FilePath, SourceSnapshot)

type Loader = StateT Loaded (ExceptT String IO)

loadProjectFile :: [FilePath] -> FilePath -> IO (Either String Project)
loadProjectFile roots path = runExceptT do
  absolute <- liftIOError "resolve" path (canonicalizePath =<< makeAbsolute path)
  source <- readSource absolute
  loadProjectSourceM roots absolute source

-- source text placed at an owner path, as standard input is.
loadProjectSource :: [FilePath] -> FilePath -> String -> IO (Either String Project)
loadProjectSource roots owner source = runExceptT do
  absolute <- liftIOError "resolve" owner (makeAbsolute owner)
  loadProjectSourceM roots absolute source

loadProjectSourceM :: [FilePath] -> FilePath -> String -> ExceptT String IO Project
loadProjectSourceM roots owner source = do
  absoluteRoots <- traverse absoluteRoot roots
  let snapshot = sourceSnapshot source
  loaded <- execStateT (discover absoluteRoots owner (takeDirectory owner) snapshot) Map.empty
  let snapshots = snd <$> loaded
  pure (Project owner source (Map.map snapshotText snapshots) (fst <$> loaded) snapshot snapshots)

discover :: [FilePath] -> FilePath -> FilePath -> SourceSnapshot -> Loader ()
discover roots owner base source = mapM_ (loadImport roots owner base) (snapshotImportPaths source)

loadImport :: [FilePath] -> FilePath -> FilePath -> FilePath -> Loader ()
loadImport roots owner base importPath = do
  candidates <- importCandidates roots base importPath
  case candidates of
    [] -> failLoader ("missing use '" ++ importPath ++ "' from '" ++ owner ++ "'")
    [candidate] -> loadCandidate candidate
    paths ->
      failLoader
        ( "ambiguous use '"
            ++ importPath
            ++ "' found at "
            ++ intercalate ", " (map (\path -> "'" ++ path ++ "'") paths)
        )
  where
    loadCandidate candidate = do
      absolute <- lift (liftIOError "resolve" candidate (canonicalizePath candidate))
      known <- gets (Map.lookup importPath)
      case known of
        Just (other, _)
          | other /= absolute ->
              failLoader
                ( "ambiguous use '"
                    ++ importPath
                    ++ "' resolveþ to both '"
                    ++ other
                    ++ "' and '"
                    ++ absolute
                    ++ "'"
                )
        _ -> pure ()
      ownerPath <- gets (fmap fst . find ((== absolute) . fst . snd) . Map.toList)
      case ownerPath of
        Just other
          | other /= importPath ->
              failLoader
                ( "use paths '"
                    ++ other
                    ++ "' and '"
                    ++ importPath
                    ++ "' resolveþ to the same file '"
                    ++ absolute
                    ++ "'"
                )
        Just _ -> pure ()
        Nothing -> do
          imported <- sourceSnapshot <$> lift (readSource absolute)
          modify' (Map.insert importPath (absolute, imported))
          discover roots absolute (takeDirectory absolute) imported

importCandidates :: [FilePath] -> FilePath -> FilePath -> Loader [FilePath]
importCandidates roots base importPath = do
  let local = normalise (base </> importPath)
  localExists <- liftIO (doesFileExist local)
  if localExists
    then pure [local]
    else filterM (liftIO . doesFileExist) [normalise (root </> importPath) | root <- roots]

absoluteRoot :: FilePath -> ExceptT String IO FilePath
absoluteRoot root = liftIOError "resolve module root" root (normalise <$> makeAbsolute root)

readSource :: FilePath -> ExceptT String IO String
readSource path = liftIOError "read" path (Text.unpack <$> Text.readFile path)

liftIOError :: String -> FilePath -> IO a -> ExceptT String IO a
liftIOError action path operation = do
  result <- liftIO (tryIOError operation)
  either (throwE . renderIoError action path . show) pure result

failLoader :: String -> Loader a
failLoader = lift . throwE

renderIoError :: String -> FilePath -> String -> String
renderIoError action path message = "cannot " ++ action ++ " '" ++ path ++ "': " ++ message
