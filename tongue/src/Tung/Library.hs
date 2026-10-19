{-# LANGUAGE OverloadedStrings #-}

-- manifest libraries supply ordinary module roots without compiler-owned names.
module Tung.Library
  ( resolveLibraryRoots,
    findManifest,
    proofAxiomPolicy,
    cacheDirectory,
    readLibraryImportFiles,
    readLibraryImports,
  )
where

import Control.Exception (finally)
import Control.Monad (foldM, forM, forM_, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), except, runExceptT, throwE)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.Aeson (FromJSON (parseJSON), withObject, (.:), (.:?))
import Data.Aeson qualified as Aeson
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types (Parser)
import Data.Char (isHexDigit, toLower)
import Data.List (find, intercalate, isInfixOf, isPrefixOf, nub, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text
import Data.Yaml qualified as Yaml
import System.Directory (canonicalizePath, createDirectoryIfMissing, doesDirectoryExist, doesFileExist, listDirectory, makeAbsolute, removeFile, removePathForcibly, renameDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (addTrailingPathSeparator, isAbsolute, normalise, splitDirectories, splitSearchPath, takeDirectory, takeExtension, (</>))
import System.IO (hClose, openTempFile)
import System.IO.Error (tryIOError)
import System.Process (readProcessWithExitCode)

data Library = Library
  { libraryName :: String,
    librarySource :: LibrarySource
  }

data LibrarySource
  = GitSource String String FilePath
  | PathSource FilePath
  deriving stock (Eq)

instance FromJSON LibrarySource where
  parseJSON = withObject "library" \fields -> do
    rejectUnknown "library" ["repo", "hash", "subdir", "path"] fields
    repository <- fields .:? "repo"
    commit <- fields .:? "hash"
    subdirectory <- fields .:? "subdir"
    path <- fields .:? "path"
    case (repository, commit, path) of
      (Just source, Just revision, Nothing) -> pure (GitSource source revision (fromMaybe "." subdirectory))
      (Nothing, Nothing, Just directory) | isNothing subdirectory -> pure (PathSource directory)
      _ -> fail "library needs either 'path' or 'repo' with 'hash' and optional 'subdir'"

data Manifest = Manifest
  { manifestLibraries :: [Library],
    manifestProofOrsettings :: Maybe [String]
  }

instance FromJSON Manifest where
  parseJSON = withObject "tung.yaml" \fields -> do
    rejectUnknown "manifest" ["dependencies", "proof"] fields
    dependencies <- fields .: "dependencies" :: Parser Aeson.Value
    libraries <- withObject "dependencies" (traverse parseEntry . KeyMap.toAscList) dependencies
    orsettings <- maybe (pure Nothing) parseProofPolicy (KeyMap.lookup "proof" fields)
    pure (Manifest libraries orsettings)
    where
      parseEntry (name, source) = Library (Key.toString name) <$> parseJSON source

parseProofPolicy :: Aeson.Value -> Parser (Maybe [String])
parseProofPolicy = withObject "proof" \fields -> do
  rejectUnknown "proof" ["orsettings"] fields
  traverse parseOrsettings (KeyMap.lookup "orsettings" fields)
  where
    parseOrsettings value = do
      names <- parseJSON value
      if names == nub names then pure names else fail "duplicate proof orsetting names"

rejectUnknown :: String -> [String] -> Aeson.Object -> Parser ()
rejectUnknown context allowed fields =
  forM_ (find (`notElem` allowed) (map Key.toString (KeyMap.keys fields))) \unknown ->
    fail ("unknown " ++ context ++ " field '" ++ unknown ++ "'")

data LibraryUse = LibraryUse
  { useName :: String,
    useSource :: LibrarySource,
    useManifest :: FilePath
  }

data SourceKey = RepositoryKey String FilePath | PathKey FilePath
  deriving stock (Eq, Ord)

data Resolved = Resolved
  { usesByName :: Map.Map String LibraryUse,
    usesBySource :: Map.Map SourceKey LibraryUse
  }

emptyResolved :: Resolved
emptyResolved = Resolved Map.empty Map.empty

-- a filesystem or git step that may fail with a message.
type Step = ExceptT String IO

type Resolver = StateT Resolved Step

-- an io action whose exception becometh a message after `context`.
attempt :: String -> IO a -> Step a
attempt context action = ExceptT (either (\failure -> Left (context ++ ": " ++ show failure)) Right <$> tryIOError action)

manifestName :: FilePath
manifestName = "tung.yaml"

resolveLibraryRoots :: FilePath -> IO (Either String [FilePath])
resolveLibraryRoots owner = runExceptT do
  pinned <- findManifestStep owner >>= maybe (pure []) \path -> evalStateT (resolveManifest (takeDirectory path </> ".tung" </> "libraries") path) emptyResolved
  configured <- lift (maybe [] (filter (not . null) . splitSearchPath) <$> lookupEnv "TUNG_PATH")
  absolute <- lift (traverse makeAbsolute configured)
  pure (nub (pinned ++ absolute))

-- the nearest project's policy governeth its audit; dependency policies do not.
proofAxiomPolicy :: FilePath -> IO (Either String (Maybe [String]))
proofAxiomPolicy owner = runExceptT (findManifestStep owner >>= maybe (pure Nothing) (fmap manifestProofOrsettings . readManifest))

-- checked interfaces live in `.tung/cache` beside the nearest `tung.yaml`,
-- or beside the file when no manifest encloseth it; git ignoreth `.tung`.
cacheDirectory :: FilePath -> IO FilePath
cacheDirectory owner = do
  start <- ownerDirectory owner
  root <- either (const start) (maybe start takeDirectory) <$> findManifest owner
  pure (root </> ".tung" </> "cache")

readLibraryImportFiles :: FilePath -> IO (Either String [(FilePath, String)])
readLibraryImportFiles owner = runExceptT (libraryImportFiles owner)

libraryImportFiles :: FilePath -> Step [(FilePath, String)]
libraryImportFiles owner = do
  roots <- ExceptT (resolveLibraryRoots owner)
  concat <$> traverse (\root -> map (\name -> (root </> name, name)) <$> discover root "") roots

readLibraryImports :: FilePath -> IO (Either String (Map.Map String String))
readLibraryImports owner = runExceptT do
  paths <- libraryImportFiles owner >>= except . foldM add Map.empty
  traverse (\path -> Text.unpack <$> attempt ("cannot read library module '" ++ path ++ "'") (Text.readFile path)) paths
  where
    add paths (path, name) = case Map.lookup name paths of
      Nothing -> Right (Map.insert name path paths)
      Just other -> Left ("library module '" ++ name ++ "' occurs at both '" ++ other ++ "' and '" ++ path ++ "'")

findManifest :: FilePath -> IO (Either String (Maybe FilePath))
findManifest = runExceptT . findManifestStep

-- the nearest `tung.yaml` at or above the owner.
findManifestStep :: FilePath -> Step (Maybe FilePath)
findManifestStep owner = lift (ownerDirectory owner) >>= search
  where
    search directory = do
      let parent = takeDirectory directory
      manifestAt directory >>= \case
        Nothing | parent /= directory -> search parent
        found -> pure found

-- a file's directory, or the owner itself when it is a directory.
ownerDirectory :: FilePath -> IO FilePath
ownerDirectory owner = do
  absolute <- makeAbsolute owner
  file <- doesFileExist absolute
  pure (if file then takeDirectory absolute else absolute)

manifestAt :: FilePath -> Step (Maybe FilePath)
manifestAt directory = lift do
  let path = directory </> manifestName
  present <- doesFileExist path
  if present then Just <$> canonicalizePath path else pure Nothing

resolveManifest :: FilePath -> FilePath -> Resolver [FilePath]
resolveManifest cache manifest = do
  libraries <- manifestLibraries <$> lift (readManifest manifest)
  fmap concat $ forM libraries \Library {libraryName, librarySource} -> do
    source <- lift (resolveSource manifest librarySource)
    known <- get
    (alreadyResolved, next) <- lift (except (registerUse known (LibraryUse libraryName source manifest)))
    put next
    if alreadyResolved
      then pure []
      else do
        root <- lift (libraryRoot cache libraryName source)
        nested <- lift (manifestAt root)
        children <- maybe (pure []) (resolveManifest cache) nested
        pure (root : children)

registerUse :: Resolved -> LibraryUse -> Either String (Bool, Resolved)
registerUse known use = do
  case Map.lookup (useName use) (usesByName known) of
    Just earlier
      | useSource earlier /= useSource use ->
          Left (sourceConflict ("library '" ++ useName use ++ "'") earlier use)
    _ -> Right ()
  let key = sourceKey (useSource use)
  case Map.lookup key (usesBySource known) of
    Just earlier
      | useName earlier /= useName use || useSource earlier /= useSource use ->
          Left (sourceConflict (sourceLabel key) earlier use)
    _ -> Right ()
  let alreadyResolved = Map.member key (usesBySource known)
      updated =
        Resolved
          { usesByName = Map.insertWith (\_ earlier -> earlier) (useName use) use (usesByName known),
            usesBySource = Map.insertWith (\_ earlier -> earlier) key use (usesBySource known)
          }
  pure (alreadyResolved, updated)

sourceKey :: LibrarySource -> SourceKey
sourceKey = \case
  GitSource repository _ subdirectory -> RepositoryKey repository subdirectory
  PathSource path -> PathKey path

sourceLabel :: SourceKey -> String
sourceLabel = \case
  RepositoryKey repository "." -> "repository '" ++ repository ++ "'"
  RepositoryKey repository subdirectory -> "repository '" ++ repository ++ "' subdirectory '" ++ subdirectory ++ "'"
  PathKey path -> "path '" ++ path ++ "'"

sourceConflict :: String -> LibraryUse -> LibraryUse -> String
sourceConflict subject earlier later =
  "conflicting sources for "
    ++ subject
    ++ ": '"
    ++ useManifest earlier
    ++ "' declares library '"
    ++ useName earlier
    ++ "' "
    ++ describeSource (useSource earlier)
    ++ ", but '"
    ++ useManifest later
    ++ "' declares library '"
    ++ useName later
    ++ "' "
    ++ describeSource (useSource later)

describeSource :: LibrarySource -> String
describeSource = \case
  GitSource repository commit "." -> "from '" ++ repository ++ "' at " ++ commit
  GitSource repository commit subdirectory -> "from '" ++ repository ++ "' at " ++ commit ++ " in '" ++ subdirectory ++ "'"
  PathSource path -> "from local path '" ++ path ++ "'"

readManifest :: FilePath -> Step Manifest
readManifest path =
  attempt ("cannot read '" ++ path ++ "'") (Yaml.decodeFileWithWarnings path)
    >>= except . \case
      Left failure -> Left (path ++ ": " ++ Yaml.prettyPrintParseException failure)
      Right (warnings, Manifest libraries orsettings)
        | not (null warnings) -> Left (path ++ ": " ++ intercalate "; " (map show warnings))
        | otherwise -> (`Manifest` orsettings) <$> traverse validateEntry libraries
  where
    validateEntry (Library name source)
      | not (validName name) = Left (path ++ ": invalid library name '" ++ name ++ "'")
      | otherwise = Library name <$> validateSource name source
    validateSource name = \case
      GitSource repository commit subdirectory
        | null repository -> Left (path ++ ": library '" ++ name ++ "' hath an empty repository")
        | not (validCommit commit) -> Left (path ++ ": library '" ++ name ++ "' needeth a full 40- or 64-digit hexadecimal commit hash")
        | isAbsolute subdirectory || ".." `elem` splitDirectories subdirectory -> Left (path ++ ": library '" ++ name ++ "' hath an invalid subdirectory")
        | otherwise -> Right (GitSource repository (map toLower commit) (normalise subdirectory))
      PathSource directory
        | null directory -> Left (path ++ ": library '" ++ name ++ "' hath an empty path")
        | otherwise -> Right (PathSource directory)
    validName name = not (null name) && all (\character -> character `elem` (['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ "-_")) name
    validCommit commit = length commit `elem` [40, 64] && all isHexDigit commit

repositoryAt :: FilePath -> String -> String
repositoryAt manifest repository
  | isAbsolute repository = normalise repository
  | "://" `isInfixOf` repository || scpStyle repository = repository
  | otherwise = normalise (takeDirectory manifest </> repository)
  where
    scpStyle value = case break (== ':') value of
      (host, ':' : _) -> not (null host) && notElem '/' host
      _ -> False

resolveSource :: FilePath -> LibrarySource -> Step LibrarySource
resolveSource manifest = \case
  GitSource repository commit subdirectory -> pure (GitSource (repositoryAt manifest repository) commit subdirectory)
  PathSource directory -> do
    let local = if isAbsolute directory then directory else takeDirectory manifest </> directory
    present <- lift (doesDirectoryExist local)
    unless present (throwE (manifest ++ ": library path '" ++ local ++ "' does not exist"))
    PathSource <$> attempt (manifest ++ ": cannot resolve library path '" ++ local ++ "'") (canonicalizePath local)

libraryRoot :: FilePath -> String -> LibrarySource -> Step FilePath
libraryRoot cache name = \case
  GitSource repository commit subdirectory -> checkout cache name repository commit >>= (`selectedSubdirectory` subdirectory)
  PathSource path -> pure path

selectedSubdirectory :: FilePath -> FilePath -> Step FilePath
selectedSubdirectory root "." = pure root
selectedSubdirectory root subdirectory = do
  let selected = root </> subdirectory
  present <- lift (doesDirectoryExist selected)
  unless present (throwE ("library subdirectory '" ++ subdirectory ++ "' does not exist in '" ++ root ++ "'"))
  (checkoutRoot, libraryPath) <- attempt ("cannot resolve library subdirectory '" ++ selected ++ "'") ((,) <$> canonicalizePath root <*> canonicalizePath selected)
  unless (addTrailingPathSeparator checkoutRoot `isPrefixOf` addTrailingPathSeparator libraryPath) (throwE ("library subdirectory '" ++ selected ++ "' escapeth checkout '" ++ checkoutRoot ++ "'"))
  pure libraryPath

-- a pinned commit is cloned once into a temporary directory and moved into
-- place; a concurrent checkout of the same commit is verified instead.
checkout :: FilePath -> String -> String -> String -> Step FilePath
checkout cache name repository commit = do
  let parent = cache </> name
      target = parent </> commit
  present <- lift (doesDirectoryExist target)
  if present
    then verify target commit
    else do
      temporary <- lift do
        createDirectoryIfMissing True parent
        (temporary, handle) <- openTempFile parent "checkout-"
        hClose handle
        removeFile temporary
        pure temporary
      let cleanup = doesDirectoryExist temporary >>= (`when` removePathForcibly temporary)
      ExceptT . (`finally` cleanup) . runExceptT $ do
        git Nothing ["clone", "--quiet", "--no-checkout", "--", repository, temporary]
        git (Just temporary) ["checkout", "--quiet", "--detach", commit]
        verify temporary commit
        lift (tryIOError (renameDirectory temporary target)) >>= \case
          Right () -> pure target
          Left failure -> do
            concurrent <- lift (doesDirectoryExist target)
            if concurrent
              then verify target commit
              else throwE ("cannot cache library checkout '" ++ target ++ "': " ++ show failure)

verify :: FilePath -> String -> Step FilePath
verify root commit = do
  actual <- git (Just root) ["rev-parse", "HEAD"]
  when (actual /= commit) (throwE ("library checkout '" ++ root ++ "' is at " ++ actual ++ ", expected " ++ commit))
  changes <- git (Just root) ["status", "--porcelain"]
  unless (null changes) (throwE ("library checkout '" ++ root ++ "' has local changes"))
  pure root

git :: Maybe FilePath -> [String] -> Step String
git directory arguments = do
  let command = maybe arguments (\root -> ["-C", root] ++ arguments) directory
  attempt ("cannot run git " ++ unwords command) (readProcessWithExitCode "git" command "") >>= \case
    (ExitSuccess, output, _) -> pure (trim output)
    (ExitFailure _, _, errorMessage) -> throwE ("git " ++ unwords command ++ ": " ++ trim errorMessage)
  where
    trim = Text.unpack . Text.strip . Text.pack

discover :: FilePath -> FilePath -> Step [FilePath]
discover root relative = do
  let directory = root </> relative
  entries <- attempt ("cannot list library root '" ++ directory ++ "'") (listDirectory directory)
  concat <$> traverse visit (sort entries)
  where
    visit entry
      | entry == ".git" || entry == ".tung" = pure []
      | otherwise = do
          let name = relative </> entry
          directory <- lift (doesDirectoryExist (root </> name))
          if directory
            then discover root name
            else pure [name | takeExtension name == ".tung"]
