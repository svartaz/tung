-- bookhoard registry, dependency, ownership, export, and type-checking invariants.
-- the graph must be acyclic, dependencies may not import ground, and each source
-- owneth at most one algebraic data declaration.
module Test.Bookhoard (group) where

import Data.Char (isAscii)
import Data.List (intercalate, isPrefixOf, nub, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, listToMaybe)
import Data.Set qualified as Set
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeBaseName, takeDirectory, takeExtension, (</>))
import Test.DependentSupport (Library, compileAs, compileWith, eraseLevels, loadLibrary, rejectContaining, sameNormalIn)
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Test.QuickCheck qualified as QuickCheck
import Tung
import Tung.Dependent qualified as Kernel
import Tung.Dependent.Source qualified as Source

group :: IO Group
group = do
  files <- readLibraryImportFiles "." >>= either fail pure
  imports <- readLibraryImports "." >>= either fail pure
  registry <- registryCase files
  loaded <- loadedSourcesCase files imports
  equality <- loadLibrary ["is.tung"]
  theorems <- loadLibrary ["ilk/list_setting.tung", "ilk/natural.tung"]
  accessibility <- loadLibrary ["ilk/accessible.tung", "ilk/zero.tung"]
  Harness.group "bookhoard" $
    registry
      : loaded
      : noUmbrellaDependencyCase files
      : groundDeedExportsCase imports
      : systemExplicitCase imports
      : runnerDeedsCase imports
      : primitiveCatalogueCase imports
      : classLayoutCase files
      : equalityCases equality
      ++ soundnessCases theorems
      ++ accessibilityCases accessibility
      ++ numberCases theorems (Map.findWithDefault "" "ilk/natural.tung" imports) (Map.findWithDefault "" "ilk/integer.tung" imports)
      ++ map (typeCase imports) (typeCheckRoots files imports)
      ++ map oneDataTypeCase (nub (map fst files))

equalityCases :: Library -> [Test]
equalityCases library =
  [ expectEq "is helpers compute on reflection" (Right [True, True, True]) do
      program <- compile "let same:[x:ℤ, ℤ] ≔ x"
      traverse
        (\expression -> sameNormalIn program expression "backbend @ℤ @+1")
        [ "same leibnitz (backbend @ℤ @+1)",
          "(backbend @ℤ @+1) evenmete",
          "(backbend @ℤ @+1) throughgo (backbend @ℤ @+1)"
        ],
    rejectContaining "throughgo requireth matching middle endpoints" "cannot unify" $
      compile "let bad ≔ (backbend @ℤ @+1) throughgo (backbend @ℤ @+2)"
  ]
  where
    compile source = compileWith library "is_test.tung" ("use is.tung\n" ++ source)

-- each ℕ host operation computeth natively on literals and unfoldeth its
-- structural model otherwise; the two must agree, and proofs may use the model.
numberCases :: Library -> String -> String -> [Test]
numberCases library natural integer =
  [ agreement "ℕ" (compileWith library "natural_model_test.tung" natural) ["is_same", "is_at_most", "eking", "offdrawing", "folding"] (0, 12) (show :: Int -> String),
    agreement "ℤ" (compileWith library "integer_model_test.tung" integer) ["is_same", "is_at_most", "eking", "offdrawing", "folding"] (-12, 12) signed,
    expectEq "a modelled operation is proved by computation and by induction" (Right ()) $
      () <$ compileWith library "natural_proof.tung" proofs
  ]
  where
    agreement label models operations range literal =
      Harness.propertyTest ("property: each " ++ label ++ " model agreeth with its native operation") $
        QuickCheck.forAll ((,,) <$> QuickCheck.elements operations <*> QuickCheck.choose range <*> QuickCheck.choose range) \(operation, left, right) ->
          let native = literal left ++ " " ++ operation ++ " " ++ literal right
           in QuickCheck.counterexample native ((models >>= \program -> agrees program operation (literal left) (literal right) native) QuickCheck.=== Right True)
    signed :: Int -> String
    signed value = (if value < 0 then "" else "+") ++ show value
    -- on literals, source checking computeth natively, so the hidden model is
    -- applied in the kernel.
    agrees program operation left right native = do
      -- a host binding and its model share universe parameters.
      (symbol, levels) <-
        Source.normaliseSourceExpression program operation >>= \case
          Kernel.Global symbol levels -> Right (symbol, levels)
          other -> Left ("not a global: " ++ show other)
      m <- Source.normaliseSourceExpression program left
      n <- Source.normaliseSourceExpression program right
      modelled <- Kernel.normalise (Source.sourceEnvironment program) (Kernel.Apply Kernel.Explicit (Kernel.Apply Kernel.Explicit (Kernel.Global (modelSymbol symbol) levels) m) n)
      expected <- Source.normaliseSourceExpression program native
      pure (eraseLevels modelled == eraseLevels expected)
    proofs =
      """
      use ilk/natural.tung
      use flock/algebra/arithmetic/hath_eke.tung
      use is.tung
      let right_zero: [n: ℕ, (n + 0) = n] ≔ backbend
      let left_zero: [n: ℕ, (0 + n) = n] ≔
        match n {
          0 ^ backbend,
          k heir ^ {x: ℕ ^ x heir} leibnitz (k left_zero)
        }
      """

-- a relation with nothing smaller is well-founded, and recursion on it runneth
-- the step once.
accessibilityCases :: Library -> [Test]
accessibilityCases library =
  [ expectEq "well-founded selfcalling computeth its step" (Right True) do
      program <- compileWith library "accessible_test.tung" source
      sameNormalIn program "answer" "4"
  ]
  where
    source =
      """
      use ilk/accessible.tung
      use ilk/zero.tung
      let never: [_: ℕ, _: ℕ, *] ≔ 𝟘
      let founded: ℕ wellgrounded never ≔ {x ^ {y, impossible ^ impossible ({}: [𝟘, ℕ accessible never y])} access}
      let answer: ℕ ≔ founded wellgrounded_selfcalling {x, _ ^ x heir} 3
      """

-- the list theorems are proved; false or ill-founded statements beside them
-- must be rejected for the stated reason, without `sorry`.
soundnessCases :: Library -> [Test]
soundnessCases library =
  [ expectEq "a closed instance of a proved setting computeth to backbend" (Right True) do
      program <-
        compile
          """
          let closed: ((1 ‥ (2 ‥ empty)) reverse $ reverse) = (1 ‥ (2 ‥ empty)) ≔ (1 ‥ (2 ‥ empty)) reverse_reverse
          let direct: ((1 ‥ (2 ‥ empty)) reverse $ reverse) = (1 ‥ (2 ‥ empty)) ≔ backbend
          """
      sameNormalIn program "closed" "direct",
    rejectContaining "a list is not its own double" "cannot unify" $
      compile "let bad: [l: ℕ list, (l · l) = l] ≔ backbend",
    rejectContaining "appending is not commutative" "cannot unify" $
      compile "let bad: [a: ℕ list, b: ℕ list, (a · b) = (b · a)] ≔ match a { empty ^ (b ·_empty) evenmete, first ‥ rest ^ (first ‥) leibnitz (rest bad b) }",
    rejectContaining "distinct lists are not same" "cannot unify 1 with 2" $
      compile "let bad: (1 ‥ empty) = (2 ‥ empty) ≔ backbend",
    rejectContaining "reversing is not the selfness" "cannot unify" $
      compile "let bad: [l: ℕ list, (l reverse) = l] ≔ match l { empty ^ backbend, first ‥ rest ^ (first ‥) leibnitz (rest bad) }",
    rejectContaining "selfcalling on the same list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ l bad",
    rejectContaining "selfcalling on a larger list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ (0 ‥ l) bad",
    rejectContaining "a branch cannot recurse on its own input" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ match l { empty ^ sorry, first ‥ rest ^ (first ‥ rest) bad }",
    rejectContaining "a half match proveth nothing" "the match is not exhaustive: missing ‥" $
      compile "let bad: [l: ℕ list, l = empty] ≔ match l { empty ^ backbend }",
    rejectContaining "an empty function needeth an impossible input" "the match is not exhaustive" $
      compile "let bad: [(1 ‥ empty) = (1 ‥ empty), 𝟘] ≔ {}",
    rejectContaining "pointwise same functions are not provably same" "cannot unify" $
      compile "let bad: [f: [ℕ, ℕ], g: [ℕ, ℕ], [n: ℕ, (n f) = (n g)], f = g] ≔ {_ ^ backbend}",
    rejectContaining "a list of one type is not a list of another" "cannot unify ℕ with" $
      compile "let bad: [ℕ list, 𝟚 list] ≔ {l ^ l}",
    rejectContaining "a host binding cannot inhabit an empty type" "requireth a different type" $
      compileAs "soundness_host.tung" "ilk void: * {}\nlet bad: void ≔ 'eke_natural' fremmed"
  ]
  where
    compile source =
      compileWith library "soundness_test.tung" $
        unlines
          [ "use is.tung",
            "use flock/algebra/whole/hath_magma.tung",
            "use ilk/list.tung",
            "use ilk/list_setting.tung",
            "use ilk/natural.tung",
            "use ilk/two.tung",
            "use ilk/zero.tung"
          ]
          ++ source

-- checking a root also checketh every module it importeth, so each module
-- needeth one reachable path through the import graph.
typeCheckRoots :: [(FilePath, String)] -> Map.Map String String -> [(FilePath, String)]
typeCheckRoots files imports = filter (\(_, name) -> name `Set.notMember` referenced) files
  where
    referenced =
      Set.fromList
        [ path
        | source <- Map.elems imports,
          Right declarations <- [Source.parseSource source],
          declaration <- declarations,
          path <- importedPaths declaration
        ]

loadedSourcesCase :: [(FilePath, String)] -> Map.Map String String -> IO Test
loadedSourcesCase files imports = do
  differences <- traverse differs files
  pure . pure $ listToMaybe (catMaybes differences)
  where
    differs (path, name) = do
      source <- readFile path
      pure $ case Map.lookup name imports of
        Just loaded | loaded == source -> Nothing
        _ -> Just ("loaded bookhoard source differs from " ++ path)

registryCase :: [(FilePath, String)] -> IO Test
registryCase registeredFiles = case lookup "ground.tung" [(name, path) | (path, name) <- registeredFiles] of
  Nothing -> pure (pure (Just "the declared bookhoard library lacks ground.tung"))
  Just groundPath -> do
    files <- discover (takeDirectory groundPath)
    let registered = sort (nub (map fst registeredFiles))
        actual = sort (filter ((== ".tung") . takeExtension) files)
    pure . pure $
      if registered == actual
        then Nothing
        else Just ("bookhoard registry differs from source tree: " ++ intercalate ", " (registered `symmetricDifference` actual))

discover :: FilePath -> IO [FilePath]
discover directory = do
  entries <- listDirectory directory
  concat <$> traverse visit entries
  where
    visit entry = do
      let path = directory </> entry
      isDirectory <- doesDirectoryExist path
      if isDirectory then discover path else pure [path]

symmetricDifference :: (Eq a) => [a] -> [a] -> [a]
symmetricDifference left right = filter (`notElem` right) left ++ filter (`notElem` left) right

typeCase :: Map.Map String String -> (FilePath, String) -> Test
typeCase imports (path, importName) = do
  source <- readFile path
  pure $ case Harness.checkSource False source imports of
    "type ok" -> Nothing
    actual -> Just ("type " ++ importName ++ ": " ++ actual)

noUmbrellaDependencyCase :: [(FilePath, String)] -> Test
noUmbrellaDependencyCase files = listToMaybe . catMaybes <$> traverse checkModule files
  where
    checkModule (_, "ground.tung") = pure Nothing
    checkModule (path, _) = do
      source <- readFile path
      pure $ case Source.parseSource source of
        Left message -> Just ("parse " ++ path ++ ": " ++ message)
        Right declarations
          | "ground.tung" `elem` concatMap importedPaths declarations -> Just (path ++ " imports the ground umbrella")
          | otherwise -> Nothing

groundDeedExportsCase :: Map.Map String String -> Test
groundDeedExportsCase imports =
  pure $ case Harness.checkSource False source imports of
    "type ok" -> Nothing
    actual -> Just ("ground deed exports: " ++ actual)
  where
    source =
      "use ground.tung "
        ++ "let echo:𝟙 deed ≔ read warp_flat { _ ^ >{then, 'a' write_line, random, 0 sleep, only sheer} } "
        ++ "let task:(ℤ task) deed ≔ (+1 sheer) fork"

systemExplicitCase :: Map.Map String String -> Test
systemExplicitCase imports =
  pure $ case Harness.checkSource False "use ground.tung let args ≔ arguments" imports of
    actual | "type error:" `isPrefixOf` actual -> Nothing
    actual -> Just ("ground unexpectedly exports system deeds: " ++ actual)

runnerDeedsCase :: Map.Map String String -> Test
runnerDeedsCase imports =
  pure $ case Harness.checkSource True source imports of
    "type ok" -> Nothing
    actual -> Just ("runner deeds: " ++ actual)
  where
    source =
      "use ground.tung use deed/clock.tung use deed/process.tung use deed/system.tung use web/server.tung use ilk/list.tung use ilk/maybe.tung "
        ++ "let route:[_: _request, _response deed] ≔ 'ok' ok $ sheer "
        ++ "let main:𝟙 deed ≔ >{then, arguments, 'TUNG_SETTING' environment, unix_time, 'true' process~run empty, 8080 serve route $ void}"

primitiveCatalogueCase :: Map.Map String String -> Test
primitiveCatalogueCase imports = pure $ case traverse Source.parseSource (Map.elems imports) of
  Left message -> Just ("primitive catalogue parse: " ++ message)
  Right programs ->
    let declarations = concat programs
        declaredForeigns = Set.fromList (concatMap foreignNames declarations)
        catalogueForeigns = Set.fromList [hostName | HostBinding {hostName} <- hostBindings]
     in if Set.size catalogueForeigns /= length hostBindings
          then Just "host catalogue repeateth a key"
          else
            if catalogueForeigns /= declaredForeigns
              then Just "host catalogue and fremmed declarations differ"
              else
                -- the evaluator performeth an argumentless binding as a deed.
                if any (argumentless . hostSignature) hostBindings
                  then Just "host catalogue containeth an argumentless binding that is not a deed"
                  else Nothing
  where
    argumentless HostSignature {hostArguments, hostResult} = null hostArguments && not (isDeed hostResult)
    isDeed (HostApp "deed" _) = True
    isDeed _ = False
    foreignNames = \case
      Source.ShownDeclaration declaration -> foreignNames declaration
      Source.HostDeclaration {Source.hostKey} -> [hostKey]
      _ -> []

oneDataTypeCase :: FilePath -> Test
oneDataTypeCase path = do
  source <- readFile path
  pure $ case Source.parseSource source of
    Left message -> Just ("parse " ++ path ++ ": " ++ message)
    Right declarations ->
      let count = length [() | declaration <- declarations, isDataDecl declaration]
       in if count <= 1 then Nothing else Just (path ++ " owneth " ++ show count ++ " data types")

importedPaths :: Source.Declaration -> [String]
importedPaths (Source.ImportDeclaration path _) = [path]
importedPaths (Source.ShownDeclaration declaration) = importedPaths declaration
importedPaths _ = []

isDataDecl :: Source.Declaration -> Bool
isDataDecl Source.InductiveDeclaration {} = True
isDataDecl (Source.ShownDeclaration declaration) = isDataDecl declaration
isDataDecl _ = False

classLayoutCase :: [(FilePath, String)] -> Test
classLayoutCase files = listToMaybe . catMaybes <$> traverse checkModule files
  where
    checkModule (path, name) = do
      source <- readFile path
      pure $ case Source.parseSource source of
        Left message -> Just ("parse " ++ path ++ ": " ++ message)
        Right declarations -> checkClasses path name (concatMap classNames declarations)
    checkClasses path name names
      | classPrefix `isPrefixOf` name = case names of
          -- a symbol flock such as `hath_+` liveth in an ascii file, `hath_eke.tung`.
          [name]
            | name == takeBaseName path -> Nothing
            | "hath_" `isPrefixOf` name, any (not . isAscii) name || any (`elem` ("+-%·" :: String)) name, "hath_" `isPrefixOf` takeBaseName path -> Nothing
          [name] -> Just (path ++ " defineth class '" ++ name ++ "'")
          _ -> Just (path ++ " owneth " ++ show (length names) ++ " classes")
      | null names = Nothing
      | otherwise = Just (path ++ " defineth a class outside the flock directory")
    classPrefix = "flock/"

classNames :: Source.Declaration -> [String]
classNames (Source.FlockDeclaration name _ _) = [name]
classNames (Source.ShownDeclaration declaration) = classNames declaration
classNames _ = []
