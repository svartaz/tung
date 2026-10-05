-- bookhoard registry, dependency, ownership, export, and type-checking invariants.
-- the graph must be acyclic, dependencies may not import ground, and each source
-- owneþ at most one algebraic data declaration.
module Test.Bookhoard (group) where

import Data.Foldable (traverse_)
import Data.List (intercalate, isPrefixOf, nub, sort, stripPrefix)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe)
import Data.Set qualified as Set
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeBaseName, takeDirectory, takeExtension, (</>))
import Test.DependentSupport (Library, compileAs, compileWith, loadLibrary, rejectContaining, sameNormalIn)
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung
import Tung.Dependent.Source qualified as Source

group :: IO Group
group = do
  files <- readLibraryImportFiles "." >>= either fail pure
  imports <- readLibraryImports "." >>= either fail pure
  registry <- registryCase files
  loaded <- loadedSourcesCase files imports
  equality <- loadLibrary ["equality.tung"]
  theorems <- loadLibrary ["ilk/list_theorem.tung", "ilk/natural.tung"]
  Harness.group "bookhoard" $
    registry
      : loaded
      : acyclicCase imports
      : noUmbrellaDependencyCase files
      : groundDeedExportsCase imports
      : systemExplicitCase imports
      : runnerDeedsCase imports
      : primitiveCatalogueCase imports
      : classLayoutCase files
      : equalityCases equality
      ++ soundnessCases theorems
      ++ map (typeCase imports) (typeCheckRoots files imports)
      ++ map oneDataTypeCase (nub (map fst files))

equalityCases :: Library -> [Test]
equalityCases library =
  [ expectEq "equality helpers compute on reflection" (Right [True, True, True]) do
      program <- compile "let same:[x:ℤ, ℤ] ≔ x"
      traverse
        (\expression -> sameNormalIn program expression "reflect @ℤ @+1")
        [ "same leibnitz (reflect @ℤ @+1)",
          "(reflect @ℤ @+1) symmetry",
          "(reflect @ℤ @+1) transitivity (reflect @ℤ @+1)"
        ],
    rejectContaining "transitivity requireþ matching middle endpoints" "cannot unify" $
      compile "let bad ≔ (reflect @ℤ @+1) transitivity (reflect @ℤ @+2)"
  ]
  where
    compile source = compileWith library "equality_test.tung" ("use equality.tung\n" ++ source)

-- þe list theorems are proved; false or ill-founded statements beside þem
-- must be rejected for þe stated reason, wiþout `sorry`.
soundnessCases :: Library -> [Test]
soundnessCases library =
  [ expectEq "a closed instance of a proved theorem computeþ to reflect" (Right True) do
      program <-
        compile
          """
          let closed: ((1 ‥ (2 ‥ empty)) reverse $ reverse) = (1 ‥ (2 ‥ empty)) ≔ (1 ‥ (2 ‥ empty)) reverse_reverse
          let direct: ((1 ‥ (2 ‥ empty)) reverse $ reverse) = (1 ‥ (2 ‥ empty)) ≔ reflect
          """
      sameNormalIn program "closed" "direct",
    rejectContaining "a list is not its own double" "cannot unify" $
      compile "let bad: [l: ℕ list, (l · l) = l] ≔ reflect",
    rejectContaining "appending is not commutative" "cannot unify" $
      compile "let bad: [a: ℕ list, b: ℕ list, (a · b) = (b · a)] ≔ match a { empty ^ (b ·_empty) symmetry, first ‥ rest ^ (first ‥) leibnitz (rest bad b) }",
    rejectContaining "distinct lists are not equal" "cannot unify 1 wiþ 2" $
      compile "let bad: (1 ‥ empty) = (2 ‥ empty) ≔ reflect",
    rejectContaining "reversing is not þe identity" "cannot unify" $
      compile "let bad: [l: ℕ list, (l reverse) = l] ≔ match l { empty ^ reflect, first ‥ rest ^ (first ‥) leibnitz (rest bad) }",
    rejectContaining "recursion on þe same list cannot prove þe empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ l bad",
    rejectContaining "recursion on a larger list cannot prove þe empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ (0 ‥ l) bad",
    rejectContaining "a branch cannot recurse on its own input" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ match l { empty ^ sorry, first ‥ rest ^ (first ‥ rest) bad }",
    rejectContaining "a partial match proveþ noþing" "the match is not exhaustive: missing ‥" $
      compile "let bad: [l: ℕ list, l = empty] ≔ match l { empty ^ reflect }",
    rejectContaining "an empty function needeþ an impossible input" "the match is not exhaustive" $
      compile "let bad: [(1 ‥ empty) = (1 ‥ empty), 𝟘] ≔ {}",
    rejectContaining "pointwise equal functions are not provably equal" "cannot unify" $
      compile "let bad: [f: [ℕ, ℕ], g: [ℕ, ℕ], [n: ℕ, (n f) = (n g)], f = g] ≔ {_ ^ reflect}",
    rejectContaining "a list of one type is not a list of anoþer" "cannot unify ℕ wiþ" $
      compile "let bad: [ℕ list, 𝟚 list] ≔ {l ^ l}",
    rejectContaining "a host binding cannot inhabit an empty type" "requireþ a different type" $
      compileAs "soundness_host.tung" "ilk void: * {}\nlet bad: void ≔ 'add_natural' fremmed"
  ]
  where
    compile source =
      compileWith library "soundness_test.tung" $
        unlines
          [ "use equality.tung",
            "use flock/algebra/total/magma.tung",
            "use ilk/list.tung",
            "use ilk/list_theorem.tung",
            "use ilk/natural.tung",
            "use ilk/two.tung",
            "use ilk/zero.tung"
          ]
          ++ source

-- checking a root also checkeþ every module it importeth, so each module
-- needeþ one reachable path through the import graph.
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

acyclicCase :: Map.Map String String -> Test
acyclicCase imports = pure $ case traverse_ (walk []) (Map.keys imports) of
  Left message -> Just message
  Right () -> Nothing
  where
    walk stack path = do
      nextStack <- enterImport stack path
      source <- maybe (Left ("missing use '" ++ path ++ "'")) Right (Map.lookup path imports)
      declarations <- either (Left . (("parse " ++ path ++ ": ") ++)) Right (Source.parseSource source)
      traverse_ (walk nextStack) (concatMap importedPaths declarations)

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
        ++ "let echo:𝟙 deed ≔ read map_flat { _ ^ >{þen, 'a' write_line, random, 0 sleep, 'x' read_file, only pure} } "
        ++ "let task:(ℤ task) deed ≔ (+1 pure) fork"

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
      "use ground.tung use deed/clock.tung use deed/process.tung use deed/system.tung use web/server.tung use ilk/list.tung use ilk/option.tung "
        ++ "let route:[_: _request, _response deed] ≔ 'ok' ok $ pure "
        ++ "let main:𝟙 deed ≔ >{þen, arguments, 'TUNG_SETTING' environment, unix_time, 'true' run_process empty, 8080 serve route $ void}"

primitiveCatalogueCase :: Map.Map String String -> Test
primitiveCatalogueCase imports = pure $ case traverse Source.parseSource (Map.elems imports) of
  Left message -> Just ("primitive catalogue parse: " ++ message)
  Right programs ->
    let declarations = concat programs
        declaredForeigns = Set.fromList (concatMap foreignNames declarations)
        catalogueForeigns = Set.fromList [hostName | HostBinding {hostName} <- hostBindings]
     in if catalogueForeigns /= declaredForeigns
          then Just "host catalogue and fremmed declarations differ"
          else
            -- þe evaluator performeþ an argumentless binding as a deed.
            if any (argumentless . hostSignature) hostBindings
              then Just "host catalogue containeþ an argumentless binding þat is not a deed"
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
       in if count <= 1 then Nothing else Just (path ++ " owneþ " ++ show count ++ " data types")

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
          -- a `haþ_` prefix separateþ a flock from its member of þe same name.
          [name] | fromMaybe name (stripPrefix "haþ_" name) == takeBaseName path -> Nothing
          [name] -> Just (path ++ " defineþ class '" ++ name ++ "'")
          _ -> Just (path ++ " owneþ " ++ show (length names) ++ " classes")
      | null names = Nothing
      | otherwise = Just (path ++ " defineþ a class outside the flock directory")
    classPrefix = "flock/"

classNames :: Source.Declaration -> [String]
classNames (Source.FlockDeclaration name _ _) = [name]
classNames (Source.ShownDeclaration declaration) = classNames declaration
classNames _ = []
