-- project loading tests filesystem discovery without involving cli presentation.
module Test.Project (group) where

import Control.Exception (bracket)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Time.Clock.POSIX (getPOSIXTime)
import System.Directory
  ( canonicalizePath,
    createDirectory,
    createDirectoryIfMissing,
    createFileLink,
    getTemporaryDirectory,
    removePathForcibly,
  )
import System.FilePath (takeDirectory, (</>))
import Test.Compile (compileProject)
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung (ModuleId (..), Project (..), loadProjectFile)
import Tung.Dependent.Source (cacheKeys, compileImports, loadInterfaces, saveInterfaces, sourceEnvironment, sourceExports, sourceSnapshot, typeOfName)

group :: IO Group
group =
  Harness.group
    "project"
    [ nestedImports,
      preparedProject,
      localImportPaths,
      moduleRootImport,
      localShadowsModuleRoot,
      ambiguousModuleRoots,
      missingImport,
      ambiguousRelativeImport,
      canonicalAlias,
      interfaceRoundTrip,
      interfaceKeys
    ]

nestedImports :: Test
nestedImports = withProject files "main.tung" \result ->
  expectEq "loadeth nested relative imports" (Right expected) (projectContents <$> result)
  where
    files =
      [ ("main.tung", "use lib/a.tung let main: [_:] ≔ only"),
        ("lib/a.tung", "use b.tung show let a ≔ b"),
        ("lib/b.tung", "show let b ≔ +1")
      ]
    expected =
      ( "use lib/a.tung let main: [_:] ≔ only",
        Map.fromList
          [ ("lib/a.tung", "use b.tung show let a ≔ b"),
            ("b.tung", "show let b ≔ +1")
          ]
      )

    projectContents project = (projectSource project, projectImports project)

preparedProject :: Test
preparedProject = withProject [("main.tung", "use dep.tung let answer ≔ worth"), ("dep.tung", "show let worth ≔ +41")] "main.tung" \case
  Left message -> pure (Just message)
  Right Project {projectPath, projectSource, projectImports} ->
    expectEq "prepared project checketh and inspecteth a type" (Right "ℤ") (compileProject (SourceModule projectPath) projectSource projectImports >>= (`typeOfName` "answer"))

localImportPaths :: Test
localImportPaths = withDirectory \root -> do
  let mainPath = root </> "main.tung"
      depPath = root </> "dep.tung"
  writeProject root [("main.tung", "use dep.tung"), ("dep.tung", "show let worth ≔ +1")]
  canonicalMain <- canonicalizePath mainPath
  canonicalDep <- canonicalizePath depPath
  result <- loadProjectFile [] mainPath
  expectEq
    "retaineth owning filesystem paths"
    (Just (canonicalMain, canonicalDep))
    ( either
        (const Nothing)
        (\Project {projectPath, projectImportPaths} -> fmap (\dep -> (projectPath, dep)) (Map.lookup "dep.tung" projectImportPaths))
        result
    )

moduleRootImport :: Test
moduleRootImport = withDirectory \root -> do
  let project = root </> "forthcast"
      modules = root </> "modules"
      source = "show let shared ≔ +7"
  writeProject root [("forthcast/main.tung", "use shared.tung"), ("modules/shared.tung", source)]
  result <- loadProjectFile [modules] (project </> "main.tung")
  expectEq "loadeth an import from a module root" (Just source) (either (const Nothing) (Map.lookup "shared.tung" . projectImports) result)

localShadowsModuleRoot :: Test
localShadowsModuleRoot = withDirectory \root -> do
  let project = root </> "forthcast"
      modules = root </> "modules"
      localSource = "show let shared ≔ +2"
  writeProject
    root
    [ ("forthcast/main.tung", "use shared.tung"),
      ("forthcast/shared.tung", localSource),
      ("modules/shared.tung", "show let shared ≔ +1")
    ]
  result <- loadProjectFile [modules] (project </> "main.tung")
  expectEq "local use precedeth a module root" (Just localSource) (either (const Nothing) (Map.lookup "shared.tung" . projectImports) result)

ambiguousModuleRoots :: Test
ambiguousModuleRoots = withDirectory \root -> do
  let project = root </> "forthcast"
      left = root </> "left"
      right = root </> "right"
  writeProject
    root
    [ ("forthcast/main.tung", "use shared.tung"),
      ("left/shared.tung", "show let left ≔ +1"),
      ("right/shared.tung", "show let right ≔ +2")
    ]
  result <- loadProjectFile [left, right] (project </> "main.tung")
  expect "rejecteth duplicate module-root matches" (either (isInfixOf "ambiguous use 'shared.tung'") (const False) result)

missingImport :: Test
missingImport = withProject [("main.tung", "use absent.tung")] "main.tung" \result ->
  expect "reporteth the owner of a missing use" (either (isInfixOf "from '") (const False) result)

ambiguousRelativeImport :: Test
ambiguousRelativeImport = withProject files "main.tung" \result ->
  expect "rejecteth one use spelling for two files" (either (isInfixOf "ambiguous use 'shared.tung'") (const False) result)
  where
    files =
      [ ("main.tung", "use left/a.tung use right/b.tung"),
        ("left/a.tung", "use shared.tung"),
        ("left/shared.tung", "show let left ≔ +1"),
        ("right/b.tung", "use shared.tung"),
        ("right/shared.tung", "show let right ≔ +2")
      ]

canonicalAlias :: Test
canonicalAlias = withDirectory \root -> do
  let mainPath = root </> "main.tung"
      sourcePath = root </> "source.tung"
      aliasPath = root </> "alias.tung"
  writeProject
    root
    [ ("main.tung", "use source.tung use alias.tung"),
      ("source.tung", "show let worth ≔ +1")
    ]
  createFileLink sourcePath aliasPath
  result <- loadProjectFile [] mainPath
  expect
    "rejecteth two import paths for one canonical file"
    (either (isInfixOf "resolveth to the same file") (const False) result)

withProject :: [(FilePath, String)] -> FilePath -> (Either String Project -> Test) -> Test
withProject files entry assertion =
  withDirectory \root -> writeProject root files >> loadProjectFile [] (root </> entry) >>= assertion

withDirectory :: (FilePath -> Test) -> Test
withDirectory action = do
  directory <- temporaryDirectory
  bracket (pure directory) removePathForcibly action

writeProject :: FilePath -> [(FilePath, String)] -> IO ()
writeProject root = mapM_ \(path, source) -> do
  let target = root </> path
  createDirectoryIfMissing True (takeDirectory target)
  writeFile target source

temporaryDirectory :: IO FilePath
temporaryDirectory = do
  base <- getTemporaryDirectory
  stamp <- round . (* 1000000) <$> getPOSIXTime
  let path = base </> ("tung-project-test-" ++ show (stamp :: Integer))
  createDirectory path
  pure path

-- a saved interface reloadeth to the same environment and exports.
interfaceRoundTrip :: Test
interfaceRoundTrip = withDirectory \root -> do
  let modules = Map.map sourceSnapshot (Map.fromList [("a.tung", "use b.tung show let a ≔ b"), ("b.tung", "show ilk two:* { one:two, other:two } show let b ≔ one")])
      keys = cacheKeys "build" modules
  case compileImports Map.empty modules ["a.tung"] of
    Left failure -> pure (Just (show failure))
    Right compiled -> do
      saveInterfaces root keys compiled
      loaded <- loadInterfaces root modules keys
      let same path = (sourceEnvironment <$> Map.lookup path loaded) == (sourceEnvironment <$> Map.lookup path compiled) && (sourceExports <$> Map.lookup path loaded) == (sourceExports <$> Map.lookup path compiled)
      expect "an interface reloadeth to the same environment and exports" (Map.keys loaded == Map.keys compiled && all same (Map.keys compiled))

-- a key changeth with its own text, an import's text, and the build, and a
-- module with a missing import hath none.
interfaceKeys :: Test
interfaceKeys =
  expectEq
    "an interface key followeth its sources and build"
    [True, True, True, True]
    [ changed (Map.insert "b.tung" "show let b ≔ +2"),
      changed (Map.insert "a.tung" "use b.tung show let a ≔ b let c ≔ a"),
      key "other" base /= key "build" base,
      Map.notMember "a.tung" (cacheKeys "build" (Map.map sourceSnapshot (Map.delete "b.tung" base)))
    ]
  where
    base = Map.fromList [("a.tung", "use b.tung show let a ≔ b"), ("b.tung", "show let b ≔ +1")]
    key build sources = Map.lookup "a.tung" (cacheKeys build (Map.map sourceSnapshot sources))
    changed edit = key "build" (edit base) /= key "build" base
