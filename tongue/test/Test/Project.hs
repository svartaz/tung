-- project loading tests filesystem discovery without involving cli presentation.
module Test.Project (group) where

import Control.Exception (bracket, evaluate)
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
import System.Mem.StableName (makeStableName)
import Test.Compile (compileProject, compileProjectWith)
import Test.DependentSupport (equalitySource)
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung (ModuleId (..), Project (..), loadEditorProject, loadProjectFile)
import Tung.Dependent (HostLiteral (..), Level (LParam), SymbolId (..), Term (Global, Literal))
import Tung.Dependent.Source (DependencyKind (..), ProofDependency (..), auditDependencies, auditProof, cacheKeys, compileImports, loadInterfaces, normaliseSourceExpression, saveInterfaces, sourceEnvironment, sourceExports, sourceGlobal, sourceSnapshot, typeOfName, verifyProof)

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
      editorProject,
      interfaceRoundTrip,
      interfaceProofAudit,
      interfaceKeys
    ]

nestedImports :: Test
nestedImports = withProject files "main.tung" \result ->
  expectEq "loadeth nested relative imports" (Right expected) (projectContents <$> result)
  where
    files =
      [ ("main.tung", "bring lib/a.tung let main: [_:] ≔ only"),
        ("lib/a.tung", "bring b.tung show let a ≔ b"),
        ("lib/b.tung", "show let b ≔ +1")
      ]
    expected =
      ( "bring lib/a.tung let main: [_:] ≔ only",
        Map.fromList
          [ ("lib/a.tung", "bring b.tung show let a ≔ b"),
            ("b.tung", "show let b ≔ +1")
          ]
      )

    projectContents project = (projectSource project, projectImports project)

preparedProject :: Test
preparedProject = withProject [("main.tung", "bring dep.tung let answer ≔ worth"), ("dep.tung", "show let worth ≔ +41")] "main.tung" \case
  Left message -> pure (Just message)
  Right Project {projectPath, projectSource, projectImports} ->
    expectEq "prepared project checketh and inspecteth a type" (Right "ℤ") (compileProject (SourceModule projectPath) projectSource projectImports >>= (`typeOfName` "answer"))

localImportPaths :: Test
localImportPaths = withDirectory \root -> do
  let mainPath = root </> "main.tung"
      depPath = root </> "dep.tung"
  writeProject root [("main.tung", "bring dep.tung"), ("dep.tung", "show let worth ≔ +1")]
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
  writeProject root [("forthcast/main.tung", "bring shared.tung"), ("modules/shared.tung", source)]
  result <- loadProjectFile [modules] (project </> "main.tung")
  expectEq "loadeth an import from a module root" (Just source) (either (const Nothing) (Map.lookup "shared.tung" . projectImports) result)

localShadowsModuleRoot :: Test
localShadowsModuleRoot = withDirectory \root -> do
  let project = root </> "forthcast"
      modules = root </> "modules"
      localSource = "show let shared ≔ +2"
  writeProject
    root
    [ ("forthcast/main.tung", "bring shared.tung"),
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
    [ ("forthcast/main.tung", "bring shared.tung"),
      ("left/shared.tung", "show let left ≔ +1"),
      ("right/shared.tung", "show let right ≔ +2")
    ]
  result <- loadProjectFile [left, right] (project </> "main.tung")
  expect "rejecteth duplicate module-root matches" (either (isInfixOf "ambiguous bring 'shared.tung'") (const False) result)

missingImport :: Test
missingImport = withProject [("main.tung", "bring missing.tung")] "main.tung" \result ->
  expect "reporteth the owner of a missing use" (either (isInfixOf "from '") (const False) result)

ambiguousRelativeImport :: Test
ambiguousRelativeImport = withProject files "main.tung" \result ->
  expect "rejecteth one use spelling for two files" (either (isInfixOf "ambiguous bring 'shared.tung'") (const False) result)
  where
    files =
      [ ("main.tung", "bring left/a.tung bring right/b.tung"),
        ("left/a.tung", "bring shared.tung"),
        ("left/shared.tung", "show let left ≔ +1"),
        ("right/b.tung", "bring shared.tung"),
        ("right/shared.tung", "show let right ≔ +2")
      ]

canonicalAlias :: Test
canonicalAlias = withDirectory \root -> do
  let mainPath = root </> "main.tung"
      sourcePath = root </> "source.tung"
      aliasPath = root </> "alias.tung"
  writeProject
    root
    [ ("main.tung", "bring source.tung bring alias.tung"),
      ("source.tung", "show let worth ≔ +1")
    ]
  createFileLink sourcePath aliasPath
  result <- loadProjectFile [] mainPath
  expect
    "rejecteth two import paths for one canonical file"
    (either (isInfixOf "resolveth to the same file") (const False) result)

-- the editor's load readeth an unsaved text before the file, and leaveth out
-- a missing or ambiguous bring for checking to report at its span.
editorProject :: Test
editorProject = withDirectory \root -> do
  writeProject
    root
    [ ("main.tung", "bring dep.tung bring missing.tung bring shared.tung"),
      ("dep.tung", "show let saved ≔ +1"),
      ("left/shared.tung", "show let left ≔ +1"),
      ("right/shared.tung", "show let right ≔ +2")
    ]
  dep <- canonicalizePath (root </> "dep.tung")
  result <- loadEditorProject [root </> "left", root </> "right"] (Map.singleton (root </> "dep.tung") "show let unsaved ≔ +2") (root </> "main.tung") "bring dep.tung bring missing.tung bring shared.tung"
  expectEq
    "an editor project readeth unsaved texts and leaveth out unresolved brings"
    (Right (Map.singleton "dep.tung" "show let unsaved ≔ +2", Map.singleton "dep.tung" dep))
    ((\Project {projectImports, projectImportPaths} -> (projectImports, projectImportPaths)) <$> result)

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

-- interfaces preserve private bodies, class registries, re-exports, and nominal
-- identities. repeated references share one symbol after checking and loading.
interfaceRoundTrip :: Test
interfaceRoundTrip = withDirectory \root -> do
  let modules = Map.map sourceSnapshot (Map.fromList sources)
      keys = cacheKeys "build" modules
  case compileImports Map.empty modules ["a.tung"] of
    Left failure -> pure (Just (show failure))
    Right compiled -> do
      saveInterfaces root keys compiled
      loaded <- loadInterfaces root modules keys
      sharing <- traverse shared [compiled, loaded]
      let same path = (sourceEnvironment <$> Map.lookup path loaded) == (sourceEnvironment <$> Map.lookup path compiled) && (sourceExports <$> Map.lookup path loaded) == (sourceExports <$> Map.lookup path compiled)
      expectEq
        "interfaces preserve checking, exports, nominal identity, and symbol sharing"
        (True, [Right expected, Right expected], [True, True])
        ( Map.keys loaded == Map.keys compiled && all same (Map.keys compiled),
          map checked [compiled, loaded],
          sharing
        )
  where
    sources =
      [ ( "a.tung",
          """
          bring b.tung base
          bring c.tung different
          show base~two
          show base~one
          show base~keep
          show base~rose_sample
          show base~depth
          show base~keeps
          show let a:base~two ≔ base~worth base~keep
          show let number ≔ base~number
          """
        ),
        ( "b.tung",
          """
          show ilk two:* { one:two, other:two }
          show flock keeps:[α:*, *] { let keep:[α, α] }
          bizen:two keeps { let keep:[x:] ≔ x }
          let secret:two ≔ one
          show let worth:two ≔ secret keep
          show let number ≔ +7
          ilk box:[α:*, *] { pack:[α, α box] }
          ilk rose:* { leaf:rose, node:[rose box, rose] }
          show let rose_sample:rose ≔ (leaf pack @rose) node
          show let depth:[rose, ℕ] ≔
            {_:rose ^ ℕ} unbuild rose {_:rose box ^ ℕ}
              0 {child:rose box ^ {below:ℕ ^ below next}}
              {child:rose ^ {below:ℕ ^ below}}
          """
        ),
        ("c.tung", "show ilk two:* { one:two }")
      ]
    checked compiled = do
      program <- rootProgram compiled
      traverse (normaliseSourceExpression program) ["answer", "number", "different~one", "shared~rose_sample shared~depth"]
    rootProgram compiled = compileProjectWith compiled RootModule rootSource Map.empty
    rootSource =
      """
      bring a.tung shared
      bring c.tung different
      let answer:shared~two ≔ shared~a shared~keep
      let number:ℤ ≔ shared~number
      """
    expected = [Global (SymbolId (SourceModule "b.tung") "one") [LParam 0], Literal (SymbolId PrimitiveModule "ℤ") (IntegerValue 7), Global (SymbolId (SourceModule "c.tung") "one") [LParam 0], Literal (SymbolId PrimitiveModule "ℕ") (NaturalValue 1)]
    shared programs = case references programs of
      Nothing -> pure False
      Just symbols -> do
        names <- traverse (\symbol -> evaluate symbol >>= makeStableName) symbols
        pure case names of
          first : rest -> all (== first) rest
          [] -> False
    references programs = do
      defining <- Map.lookup "b.tung" programs
      using <- either (const Nothing) Just (rootProgram programs)
      original <- sourceGlobal defining "one"
      exported <- sourceGlobal using "shared~one"
      case normaliseSourceExpression using "answer" of
        Right (Global used _) -> Just [original, exported, used]
        _ -> Nothing

interfaceProofAudit :: Test
interfaceProofAudit = withDirectory \root -> do
  let modules = Map.map sourceSnapshot (Map.fromList sources)
      keys = cacheKeys "proof-audit" modules
  case compileImports Map.empty modules ["a.tung"] of
    Left failure -> pure (Just (show failure))
    Right compiled -> do
      saveInterfaces root keys compiled
      loaded <- loadInterfaces root modules keys
      expectEq
        "proof dependencies and policies survive a disk interface round trip"
        [Right expected, Right expected]
        (map checked [compiled, loaded])
  where
    sources =
      [ ("a.tung", "bring b.tung source\nshow source~visible\nshow source~computed\nshow let theorem:ℕ ≔ source~secret"),
        ( "b.tung",
          equalitySource
            ++ """
               show orsetting visible:ℕ
               orsetting hidden:ℕ
               let ignore:[ℕ,*] ≔ {_ ^ ℕ}
               let annotation:* ≔ hidden ignore
               show let secret:annotation ≔ 0
               let add:[ℕ,ℕ,ℕ] ≔ 'eke_kindful' fremmed
               show let computed:(0 add 0) = 0 ≔ eftbend
               """
        )
      ]
    source = "bring a.tung shared\nlet selected:ℕ ≔ shared~theorem\nlet allowed:ℕ ≔ shared~visible\nlet computed ≔ shared~computed"
    checked compiled = do
      program <- compileProjectWith compiled RootModule source Map.empty
      selected <- auditProof program "selected"
      allowed <- auditProof program "allowed"
      computed <- auditProof program "computed"
      pure
        ( [[(dependencySymbol, dependencyKind) | ProofDependency {..} <- auditDependencies audited] | audited <- [selected, allowed, computed]],
          verifyProof program True Nothing selected,
          verifyProof program True (Just ["shared~visible"]) allowed
        )
    expected =
      ( [[(SymbolId (SourceModule "b.tung") "hidden", AxiomDependency)], [(SymbolId (SourceModule "b.tung") "visible", AxiomDependency)], [(SymbolId (SourceModule "b.tung") "add", HostDependency "eke_kindful")]],
        Right (),
        Right ()
      )

-- a key changeth with its own text, an import's text, and the build, and a
-- module with a missing import hath none.
interfaceKeys :: Test
interfaceKeys =
  expectEq
    "an interface key followeth its sources and build"
    [True, True, True, True]
    [ changed (Map.insert "b.tung" "show let b ≔ +2"),
      changed (Map.insert "a.tung" "bring b.tung show let a ≔ b let c ≔ a"),
      key "other" base /= key "build" base,
      Map.notMember "a.tung" (cacheKeys "build" (Map.map sourceSnapshot (Map.delete "b.tung" base)))
    ]
  where
    base = Map.fromList [("a.tung", "bring b.tung show let a ≔ b"), ("b.tung", "show let b ≔ +1")]
    key build sources = Map.lookup "a.tung" (cacheKeys build (Map.map sourceSnapshot sources))
    changed edit = key "build" (edit base) /= key "build" base
