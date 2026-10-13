-- local paths and pinned git checkouts supply ordinary modules.
module Test.Library (group) where

import Control.Exception (bracket)
import Control.Monad (void)
import Data.Char (toUpper)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Time.Clock.POSIX (getPOSIXTime)
import System.Directory (canonicalizePath, createDirectory, createDirectoryIfMissing, createDirectoryLink, getTemporaryDirectory, removePathForcibly, renameDirectory)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, takeFileName, (</>))
import System.Process (readProcessWithExitCode)
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung (loadProjectFile, projectImports, proofAxiomPolicy, resolveLibraryRoots)

group :: IO Group
group =
  Harness.group "library" $
    [pinnedCheckout, gitSubdirectory, distinctGitSubdirectories, conflictingGitSubdirectoryNames, escapedGitSubdirectory, localPathDependency, transitivePathDependency, sharedTransitivePin, conflictingTransitivePins, conflictingAliasedPins, conflictingRepositoryNames, conflictingLibrarySources, conflictingPathNames, conflictingPathAndGitSources, invalidManifest, invalidPathSource, duplicateManifestKey, unknownManifestField, malformedManifest, transitiveCheckout, proofPolicyForms, proofPolicyNearestProject]
      ++ map
        (uncurry invalidProofPolicy)
        [ ("null", "expected Object"),
          ("{ axiom: [] }", "unknown proof field 'axiom'"),
          ("{ axioms: null }", "expected Array"),
          ("{ axioms: [1] }", "expected String"),
          ("{ axioms: [trusted, trusted] }", "duplicate proof axiom names")
        ]

proofPolicyForms :: Test
proofPolicyForms = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  absent <- proofAxiomPolicy owner
  forms <-
    traverse
      ( \policy -> do
          writeFile (root </> "tung.yaml") ("dependencies: {}\n" ++ policy)
          proofAxiomPolicy owner
      )
      ["", "proof: {}\n", "proof: { axioms: [] }\n", "proof: { axioms: [trusted, 'often~≍_to_='] }\n"]
  expectEq
    "distinguish absent and empty proof axiom policies and preserve names"
    [Right Nothing, Right Nothing, Right Nothing, Right (Just []), Right (Just ["trusted", "often~≍_to_="])]
    (absent : forms)

proofPolicyNearestProject :: Test
proofPolicyNearestProject = withDirectory \root -> do
  let library = root </> "library"
      project = root </> "forthcast"
      source = project </> "src"
      owner = source </> "main.tung"
      dependencies = "dependencies: { sample: { path: ../library } }\n"
  mapM_ (createDirectoryIfMissing True) [library, source]
  writeFile owner "let answer ≔ +1"
  writeFile (root </> "tung.yaml") "dependencies: {}\nproof: { axioms: [outer] }\n"
  writeFile (library </> "tung.yaml") "dependencies: {}\nproof: { axioms: [] }\n"
  writeFile (project </> "tung.yaml") (dependencies ++ "proof: { axioms: [trusted] }\n")
  selected <- proofAxiomPolicy owner
  roots <- resolveLibraryRoots owner
  writeFile (project </> "tung.yaml") dependencies
  absent <- proofAxiomPolicy owner
  expectedRoot <- canonicalizePath library
  expectEq
    "only the nearest project manifest governeth its proof policy"
    (Right (Just ["trusted"]), Right [expectedRoot], Right Nothing)
    (selected, roots, absent)

invalidProofPolicy :: String -> String -> Test
invalidProofPolicy policy fragment = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile (root </> "tung.yaml") ("dependencies: {}\nproof: " ++ policy ++ "\n")
  selected <- proofAxiomPolicy owner
  roots <- resolveLibraryRoots owner
  expect ("rejecteth malformed proof policy " ++ policy) $
    all (either (isInfixOf fragment) (const False)) [() <$ selected, () <$ roots]

pinnedCheckout :: Test
pinnedCheckout = withDirectory \root -> do
  let repository = root </> "source"
      project = root </> "forthcast"
      owner = project </> "main.tung"
      libraryFile = repository </> "worth.tung"
      manifest = project </> "tung.yaml"
  initRepository repository
  createDirectory project
  writeFile libraryFile "show let worth ≔ +41"
  commitAll repository "first"
  commit <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile manifest (yamlManifest [("sample", "file://" ++ repository, map toUpper commit)])
  writeFile owner "bring worth.tung let answer ≔ worth + +1"
  first <- resolveLibraryRoots owner
  imported <- case first of
    Left message -> pure (Left message)
    Right roots -> do
      projectResult <- loadProjectFile roots owner
      pure (Map.lookup "worth.tung" . projectImports <$> projectResult)
  writeFile libraryFile "show let worth ≔ +99"
  commitAll repository "second"
  renameDirectory repository (root </> "source-moved")
  offline <- resolveLibraryRoots owner
  pure $ case (first, imported, offline) of
    (Right [firstRoot], Right (Just "show let worth ≔ +41"), Right [offlineRoot]) ->
      if firstRoot == offlineRoot then Nothing else Just "git library cache changed after its source moved"
    other -> Just ("pinned git library failed: " ++ show other)

gitSubdirectory :: Test
gitSubdirectory = withDirectory \root -> do
  let repository = root </> "source"
      library = repository </> "bookhoard"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository repository
  createDirectory library
  createDirectory project
  writeFile (library </> "worth.tung") "show let worth ≔ +42"
  writeFile (repository </> "outside.tung") "show let outside ≔ +0"
  commitAll repository "bookhoard"
  commit <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile (project </> "tung.yaml") (yamlSubdirManifest [("bookhoard", repository, commit, "bookhoard")])
  writeFile owner "bring worth.tung let answer ≔ worth"
  roots <- resolveLibraryRoots owner
  imported <- importedSource roots owner "worth.tung"
  pure $ case (roots, imported) of
    (Right [libraryRoot], Right (Just "show let worth ≔ +42"))
      | takeFileName libraryRoot == "bookhoard" -> Nothing
    other -> Just ("git library subdirectory failed: " ++ show other)

distinctGitSubdirectories :: Test
distinctGitSubdirectories = withDirectory \root -> do
  let repository = root </> "source"
      first = repository </> "first"
      second = repository </> "second"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository repository
  mapM_ createDirectory [first, second, project]
  writeFile (first </> "first.tung") "show let one ≔ +1"
  writeFile (second </> "second.tung") "show let two ≔ +2"
  commitAll repository "two libraries"
  commit <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile (project </> "tung.yaml") (yamlSubdirManifest [("first", repository, commit, "first"), ("second", repository, commit, "second")])
  writeFile owner "bring first.tung bring second.tung let answer ≔ one + two"
  roots <- resolveLibraryRoots owner
  one <- importedSource roots owner "first.tung"
  two <- importedSource roots owner "second.tung"
  pure $ case (roots, one, two) of
    (Right [_, _], Right (Just "show let one ≔ +1"), Right (Just "show let two ≔ +2")) -> Nothing
    other -> Just ("distinct git subdirectories failed: " ++ show other)

conflictingGitSubdirectoryNames :: Test
conflictingGitSubdirectoryNames = withDirectory \root -> do
  let repository = root </> "source"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository repository
  createDirectory (repository </> "library")
  createDirectory project
  writeFile (repository </> "library" </> "worth.tung") "show let worth ≔ +1"
  commitAll repository "library"
  commit <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile (project </> "tung.yaml") (yamlSubdirManifest [("first", repository, commit, "library"), ("second", repository, commit, "library")])
  writeFile owner "let answer ≔ +1"
  result <- resolveLibraryRoots owner
  expect "rejecteth two names for one git subdirectory" $
    either (\message -> all (`isInfixOf` message) ["repository '" ++ repository ++ "' subdirectory 'library'", "library 'first'", "library 'second'"]) (const False) result

escapedGitSubdirectory :: Test
escapedGitSubdirectory = withDirectory \root -> do
  let repository = root </> "source"
      outside = root </> "outside"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository repository
  createDirectory outside
  createDirectory project
  createDirectoryLink outside (repository </> "escape")
  commitAll repository "symlink"
  commit <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile (project </> "tung.yaml") (yamlSubdirManifest [("escape", repository, commit, "escape")])
  writeFile owner "let answer ≔ +1"
  result <- resolveLibraryRoots owner
  expect "rejecteth a git library subdirectory outside its checkout" $
    either (isInfixOf "escapeth checkout") (const False) result

localPathDependency :: Test
localPathDependency = withDirectory \root -> do
  let library = root </> "source"
      project = root </> "forthcast"
      owner = project </> "main.tung"
      source = library </> "worth.tung"
  createDirectory library
  createDirectory project
  writeFile source "show let worth ≔ +41"
  writeFile
    (project </> "tung.yaml")
    """
    dependencies:
      sample:
        path: ../source

    """
  writeFile owner "bring worth.tung let answer ≔ worth + +1"
  first <- resolveLibraryRoots owner
  firstImport <- importedSource first owner "worth.tung"
  writeFile source "show let worth ≔ +99"
  second <- resolveLibraryRoots owner
  secondImport <- importedSource second owner "worth.tung"
  expected <- canonicalizePath library
  pure $ case (first, firstImport, second, secondImport) of
    (Right [firstRoot], Right (Just "show let worth ≔ +41"), Right [secondRoot], Right (Just "show let worth ≔ +99"))
      | firstRoot == expected && secondRoot == expected -> Nothing
    other -> Just ("local library path failed: " ++ show other)

transitivePathDependency :: Test
transitivePathDependency = withDirectory \root -> do
  let dependency = root </> "dependency"
      parent = root </> "parent"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  mapM_ createDirectory [dependency, parent, project]
  writeFile (dependency </> "dep.tung") "show let answer ≔ +42"
  writeFile (parent </> "parent.tung") "bring dep.tung show let worth ≔ answer"
  writeFile
    (parent </> "tung.yaml")
    """
    dependencies:
      dependency:
        path: ../dependency

    """
  writeFile
    (project </> "tung.yaml")
    """
    dependencies:
      parent:
        path: ../parent

    """
  writeFile owner "bring parent.tung let outcome ≔ worth"
  roots <- resolveLibraryRoots owner
  imported <- importedSource roots owner "dep.tung"
  pure $ case (roots, imported) of
    (Right [_, _], Right (Just "show let answer ≔ +42")) -> Nothing
    other -> Just ("throughgo local path failed: " ++ show other)

importedSource :: Either String [FilePath] -> FilePath -> FilePath -> IO (Either String (Maybe String))
importedSource (Left message) _ _ = pure (Left message)
importedSource (Right roots) owner name = do
  project <- loadProjectFile roots owner
  pure (Map.lookup name . projectImports <$> project)

invalidManifest :: Test
invalidManifest = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile (root </> "tung.yaml") (yamlManifest [("sample", "../source", "main")])
  result <- resolveLibraryRoots owner
  expect "rejecteth a moving git revision" (either (const True) (const False) result)

duplicateManifestKey :: Test
duplicateManifestKey = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile
    (root </> "tung.yaml")
    """
    dependencies:
      sample:
        repo: ../first
        hash: abc
      sample:
        repo: ../second
        hash: def

    """
  result <- resolveLibraryRoots owner
  expect "rejecteth duplicate yaml dependency names" $
    either (isInfixOf "DuplicateKey") (const False) result

unknownManifestField :: Test
unknownManifestField = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile
    (root </> "tung.yaml")
    """
    dependencies:
      sample:
        repository: ../source
        hash: abc

    """
  result <- resolveLibraryRoots owner
  expect "rejecteth misspelled yaml fields" $
    either (isInfixOf "unknown library field 'repository'") (const False) result

malformedManifest :: Test
malformedManifest = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile (root </> "tung.yaml") "dependencies: [\n"
  result <- resolveLibraryRoots owner
  expect "rejecteth malformed yaml" (either (const True) (const False) result)

transitiveCheckout :: Test
transitiveCheckout = withDirectory \root -> do
  let dependency = root </> "dependency"
      parent = root </> "parent"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository dependency
  writeFile (dependency </> "dep.tung") "show let answer ≔ +42"
  commitAll dependency "dependency"
  dependencyCommit <- runGit ["-C", dependency, "rev-parse", "HEAD"]
  initRepository parent
  writeFile (parent </> "parent.tung") "bring dep.tung show let worth ≔ answer"
  writeFile (parent </> "tung.yaml") (yamlManifest [("dependency", dependency, dependencyCommit)])
  commitAll parent "parent"
  parentCommit <- runGit ["-C", parent, "rev-parse", "HEAD"]
  createDirectory project
  writeFile (project </> "tung.yaml") (yamlManifest [("parent", "../parent", parentCommit)])
  writeFile owner "bring parent.tung let outcome ≔ worth"
  resolved <- resolveLibraryRoots owner
  imported <- case resolved of
    Left message -> pure (Left message)
    Right roots -> do
      projectResult <- loadProjectFile roots owner
      pure (Map.lookup "dep.tung" . projectImports <$> projectResult)
  pure $ case (resolved, imported) of
    (Right [_, _], Right (Just "show let answer ≔ +42")) -> Nothing
    other -> Just ("throughgo git library failed: " ++ show other)

sharedTransitivePin :: Test
sharedTransitivePin = withDirectory \root -> do
  (repository, first, _) <- dependencyVersions root
  owner <- createDiamond root repository first "shared" first
  result <- resolveLibraryRoots owner
  expect "shareth one checkout for an agreed throughgo pin" (either (const False) ((== 3) . length) result)

conflictingTransitivePins :: Test
conflictingTransitivePins = withDirectory \root -> do
  (repository, first, second) <- dependencyVersions root
  owner <- createDiamond root repository first "shared" second
  result <- resolveLibraryRoots owner
  expect "rejecteth conflicting throughgo pins before import" $
    either (\message -> all (`isInfixOf` message) ["library 'shared'", first, second]) (const False) result

conflictingAliasedPins :: Test
conflictingAliasedPins = withDirectory \root -> do
  (repository, first, second) <- dependencyVersions root
  owner <- createDiamond root repository first "renamed" second
  result <- resolveLibraryRoots owner
  expect "rejecteth different aliases for two versions of one repository" $
    either (\message -> all (`isInfixOf` message) ["repository '" ++ repository ++ "'", first, second]) (const False) result

conflictingRepositoryNames :: Test
conflictingRepositoryNames = withDirectory \root -> do
  (repository, commit, _) <- dependencyVersions root
  owner <- createDiamond root repository commit "renamed" commit
  result <- resolveLibraryRoots owner
  expect "rejecteth two names for one library repository" $
    either (\message -> all (`isInfixOf` message) ["repository '" ++ repository ++ "'", "library 'shared'", "library 'renamed'"]) (const False) result

conflictingLibrarySources :: Test
conflictingLibrarySources = withDirectory \root -> do
  (firstRepository, firstCommit, _) <- dependencyVersions root
  let other = root </> "other"
  createDirectory other
  (secondRepository, secondCommit, _) <- dependencyVersions other
  owner <- createDiamondWith root (firstRepository, "shared", firstCommit) (secondRepository, "shared", secondCommit)
  result <- resolveLibraryRoots owner
  expect "rejecteth one library name from two repositories" $
    either (\message -> all (`isInfixOf` message) ["library 'shared'", firstRepository, secondRepository]) (const False) result

conflictingPathNames :: Test
conflictingPathNames = withDirectory \root -> do
  let source = root </> "source"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  createDirectory source
  createDirectory project
  writeFile owner "let answer ≔ +1"
  writeFile
    (project </> "tung.yaml")
    """
    dependencies:
      first:
        path: ../source
      second:
        path: ../source

    """
  resolved <- canonicalizePath source
  result <- resolveLibraryRoots owner
  expect "rejecteth two names for one local library path" $
    either (\message -> all (`isInfixOf` message) ["path '" ++ resolved ++ "'", "library 'first'", "library 'second'"]) (const False) result

conflictingPathAndGitSources :: Test
conflictingPathAndGitSources = withDirectory \root -> do
  let source = root </> "source"
      parent = root </> "parent"
      project = root </> "forthcast"
      owner = project </> "main.tung"
  initRepository source
  writeFile (source </> "worth.tung") "show let worth ≔ +1"
  commitAll source "source"
  commit <- runGit ["-C", source, "rev-parse", "HEAD"]
  createDirectory parent
  writeFile (parent </> "tung.yaml") (yamlManifest [("shared", source, commit)])
  createDirectory project
  writeFile
    (project </> "tung.yaml")
    """
    dependencies:
      parent:
        path: ../parent
      shared:
        path: ../source

    """
  writeFile owner "let answer ≔ +1"
  result <- resolveLibraryRoots owner
  expect "rejecteth a local path and git pin for one library name" $
    either (\message -> all (`isInfixOf` message) ["library 'shared'", commit, "local path"]) (const False) result

invalidPathSource :: Test
invalidPathSource = withDirectory \root -> do
  let owner = root </> "main.tung"
  writeFile owner "let answer ≔ +1"
  writeFile
    (root </> "tung.yaml")
    """
    dependencies:
      sample:
        path: missing

    """
  missing <- resolveLibraryRoots owner
  writeFile
    (root </> "tung.yaml")
    """
    dependencies:
      sample:
        path: .
        repo: elsewhere
        hash: '0123456789012345678901234567890123456789'

    """
  mixed <- resolveLibraryRoots owner
  expect "rejecteth missing and mixed library sources" $
    either (isInfixOf "does not exist") (const False) missing
      && either (isInfixOf "either 'path' or 'repo' with 'hash' and optional 'subdir'") (const False) mixed

dependencyVersions :: FilePath -> IO (FilePath, String, String)
dependencyVersions root = do
  let repository = root </> "dependency"
      source = repository </> "dep.tung"
  initRepository repository
  writeFile source "show let answer ≔ +1"
  commitAll repository "first"
  first <- runGit ["-C", repository, "rev-parse", "HEAD"]
  writeFile source "show let answer ≔ +2"
  commitAll repository "second"
  second <- runGit ["-C", repository, "rev-parse", "HEAD"]
  pure (repository, first, second)

createDiamond :: FilePath -> FilePath -> String -> String -> String -> IO FilePath
createDiamond root dependency first secondName second =
  createDiamondWith root (dependency, "shared", first) (dependency, secondName, second)

createDiamondWith :: FilePath -> (FilePath, String, String) -> (FilePath, String, String) -> IO FilePath
createDiamondWith root left right = do
  parents <- traverse createParent [("left", left), ("right", right)]
  let project = root </> "forthcast"
      owner = project </> "main.tung"
  createDirectory project
  writeFile (project </> "tung.yaml") (yamlManifest [(name, "../" ++ name, commit) | (name, commit) <- parents])
  writeFile owner "let answer ≔ +1"
  pure owner
  where
    createParent (name, (dependency, dependencyName, commit)) = do
      let repository = root </> name
      initRepository repository
      writeFile (repository </> "tung.yaml") (yamlManifest [(dependencyName, dependency, commit)])
      commitAll repository name
      parentCommit <- runGit ["-C", repository, "rev-parse", "HEAD"]
      pure (name, parentCommit)

yamlManifest :: [(String, String, String)] -> String
yamlManifest entries =
  "dependencies:\n"
    ++ concat
      [ "  " ++ name ++ ":\n    repo: " ++ show repository ++ "\n    hash: " ++ show commit ++ "\n"
      | (name, repository, commit) <- entries
      ]

yamlSubdirManifest :: [(String, String, String, FilePath)] -> String
yamlSubdirManifest entries =
  "dependencies:\n"
    ++ concat
      [ "  " ++ name ++ ":\n    repo: " ++ show repository ++ "\n    hash: " ++ show commit ++ "\n    subdir: " ++ show subdirectory ++ "\n"
      | (name, repository, commit, subdirectory) <- entries
      ]

initRepository :: FilePath -> IO ()
initRepository repository = do
  createDirectory repository
  runGit ["init", "--quiet", repository]
  runGit ["-C", repository, "config", "user.name", "Tung Test"]
  void (runGit ["-C", repository, "config", "user.email", "tung-test@example.invalid"])

commitAll :: FilePath -> String -> IO ()
commitAll repository message = do
  runGit ["-C", repository, "add", "."]
  void (runGit ["-C", repository, "commit", "--quiet", "-m", message])

withDirectory :: (FilePath -> Test) -> Test
withDirectory action = bracket temporary removePathForcibly action
  where
    temporary = do
      directory <- getTemporaryDirectory
      stamp <- round . (* 1000000) <$> getPOSIXTime
      let path = directory </> ("tung-library-test-" ++ show (stamp :: Integer))
      createDirectoryIfMissing True (takeDirectory path)
      createDirectory path
      pure path

runGit :: [String] -> IO String
runGit arguments = do
  (status, output, errors) <- readProcessWithExitCode "git" arguments ""
  case status of
    ExitSuccess -> pure (filter (/= '\n') output)
    ExitFailure _ -> fail ("git " ++ unwords arguments ++ ": " ++ errors)
