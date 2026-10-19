-- | filesystem project loading is kept outside parsing and import semantics.
-- the loader resolveth relative imports into the flat source bundle consumed by the
-- checker, and rejecteth path collisions instead of silently choosing one file.
-- the editor's load readeth unsaved texts first and leaveth out a bring it
-- cannot resolve, so checking reporteth it at its span.
module Tung.Project
  ( Project (..),
    loadProjectFile,
    loadProjectSource,
    loadEditorProject,
  )
where

import Control.Monad (filterM, unless)
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

-- a root source and every source it reacheth, keyed by `use` path, with the
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

-- module roots, unsaved texts by canonical path, and whether an unresolved
-- bring is left out rather than refused.
data Loading = Loading
  { loadingRoots :: [FilePath],
    loadingTexts :: Map.Map FilePath String,
    loadingLenient :: Bool
  }

loadProjectFile :: [FilePath] -> FilePath -> IO (Either String Project)
loadProjectFile roots path = runExceptT do
  absolute <- liftIOError "resolve" path (canonicalizePath =<< makeAbsolute path)
  source <- readSource Map.empty absolute
  loadProjectSourceM (Loading roots Map.empty False) absolute source

-- source text placed at an owner path, as standard input is.
loadProjectSource :: [FilePath] -> FilePath -> String -> IO (Either String Project)
loadProjectSource roots owner source = runExceptT do
  absolute <- liftIOError "resolve" owner (makeAbsolute owner)
  loadProjectSourceM (Loading roots Map.empty False) absolute source

-- an editor document with the unsaved texts of open files. it faileth only
-- when a module root cannot be resolved.
loadEditorProject :: [FilePath] -> Map.Map FilePath String -> FilePath -> String -> IO (Either String Project)
loadEditorProject roots texts owner source = runExceptT do
  absolute <- liftIOError "resolve" owner (makeAbsolute owner)
  canonical <- Map.fromList <$> traverse (\(path, text) -> (,text) <$> liftIOError "resolve" path (canonicalizePath path)) (Map.toList texts)
  loadProjectSourceM (Loading roots canonical True) absolute source

loadProjectSourceM :: Loading -> FilePath -> String -> ExceptT String IO Project
loadProjectSourceM loading owner source = do
  absoluteRoots <- traverse absoluteRoot (loadingRoots loading)
  let snapshot = sourceSnapshot source
  loaded <- execStateT (discover loading {loadingRoots = absoluteRoots} owner (takeDirectory owner) snapshot) Map.empty
  let snapshots = snd <$> loaded
  pure (Project owner source (Map.map snapshotText snapshots) (fst <$> loaded) snapshot snapshots)

discover :: Loading -> FilePath -> FilePath -> SourceSnapshot -> Loader ()
discover loading owner base source = mapM_ (loadImport loading owner base) (snapshotImportPaths source)

loadImport :: Loading -> FilePath -> FilePath -> FilePath -> Loader ()
loadImport loading owner base importPath = do
  candidates <- importCandidates (loadingRoots loading) base importPath
  case candidates of
    [] -> refuse ("missing bring '" ++ importPath ++ "' from '" ++ owner ++ "'")
    [candidate] -> loadCandidate candidate
    paths ->
      refuse
        ( "ambiguous bring '"
            ++ importPath
            ++ "' found at "
            ++ intercalate ", " (map (\path -> "'" ++ path ++ "'") paths)
        )
  where
    refuse = unless (loadingLenient loading) . failLoader
    loadCandidate candidate = do
      absolute <- lift (liftIOError "resolve" candidate (canonicalizePath candidate))
      known <- gets (Map.lookup importPath)
      ownerPath <- gets (fmap fst . find ((== absolute) . fst . snd) . Map.toList)
      case (known, ownerPath) of
        (Just (other, _), _)
          | other /= absolute ->
              refuse
                ( "ambiguous bring '"
                    ++ importPath
                    ++ "' resolveth to both '"
                    ++ other
                    ++ "' and '"
                    ++ absolute
                    ++ "'"
                )
        (_, Just other)
          | other /= importPath ->
              refuse
                ( "bring paths '"
                    ++ other
                    ++ "' and '"
                    ++ importPath
                    ++ "' resolveth to the same file '"
                    ++ absolute
                    ++ "'"
                )
        (_, Just _) -> pure ()
        (_, Nothing) -> do
          imported <- sourceSnapshot <$> lift (readSource (loadingTexts loading) absolute)
          modify' (Map.insert importPath (absolute, imported))
          discover loading absolute (takeDirectory absolute) imported

importCandidates :: [FilePath] -> FilePath -> FilePath -> Loader [FilePath]
importCandidates roots base importPath = do
  let local = normalise (base </> importPath)
  localExists <- liftIO (doesFileExist local)
  if localExists
    then pure [local]
    else filterM (liftIO . doesFileExist) [normalise (root </> importPath) | root <- roots]

absoluteRoot :: FilePath -> ExceptT String IO FilePath
absoluteRoot root = liftIOError "resolve module root" root (normalise <$> makeAbsolute root)

readSource :: Map.Map FilePath String -> FilePath -> ExceptT String IO String
readSource texts path = maybe (liftIOError "read" path (Text.unpack <$> Text.readFile path)) pure (Map.lookup path texts)

liftIOError :: String -> FilePath -> IO a -> ExceptT String IO a
liftIOError action path operation = liftIO (tryIOError operation) >>= either (throwE . renderIoError action path . show) pure

failLoader :: String -> Loader a
failLoader = lift . throwE

renderIoError :: String -> FilePath -> String -> String
renderIoError action path message = "cannot " ++ action ++ " '" ++ path ++ "': " ++ message
