-- bookhoard registry, dependency, ownership, export, and type-checking invariants.
-- the graph must be acyclic, dependencies may not import ground, and each source
-- owneth at most one algebraic data declaration.
module Test.Bookhoard (group) where

import Data.List (intercalate, isPrefixOf, nub, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, listToMaybe)
import Data.Set qualified as Set
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeBaseName, takeDirectory, takeExtension, (</>))
import Test.DependentSupport (Library, compileAs, compileWith, eraseLevels, libraryModule, loadLibrary, rejectContaining, sameNormalIn)
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
  -- every module is checked once, including disconnected cycles and private bodies.
  library <- loadLibrary (Map.keys imports)
  Harness.group "bookhoard" $
    registry
      : loaded
      : noUmbrellaDependencyCase files
      : groundDeedExportsCase imports
      : systemExplicitCase imports
      : runnerDeedsCase imports
      : primitiveCatalogueCase imports
      : classLayoutCase files
      : equalityCases library
      ++ soundnessCases library
      ++ accessibilityCases library
      ++ yonedaCases library
      ++ moduleCases library
      ++ groupCases library
      ++ setCases library
      ++ numberCases library
      ++ [oneDataTypeCase (nub (map fst files))]

equalityCases :: Library -> [Test]
equalityCases library =
  [ expectEq "is helpers compute on reflection" (Right [True, True, True]) do
      program <- compile "let same:[x:ℤ, ℤ] ≔ x"
      traverse
        (\expression -> sameNormalIn program expression "eftbend @ℤ @+1")
        [ "same leibnitz (eftbend @ℤ @+1)",
          "(eftbend @ℤ @+1) evenmete",
          "(eftbend @ℤ @+1) throughgo (eftbend @ℤ @+1)"
        ],
    expectEq "library identity supporteth arbitrary types and dependent throughbear" (Right ()) $
      ()
        <$ compile
          """
          let reflect_value:[@α:*, x:α, x = x] ≔ eftbend
          let reflect_type:[@α:*, α = α] ≔ eftbend
          let shift_type:[@α:*, @β:*, eftbend:α = β, α, β] ≔ {x ^ x}
          let shift_value:[@α:*, @a:α, @b:α, @P:[α,*], p:a = b, value:a P, b P] ≔ p throughbear value
          """,
    rejectContaining "library identity doth not provide axiom K" "axiom K" $
      compile "let k:[@α:*, @a:α, p:a = a, p = eftbend] ≔ match p { eftbend ^ eftbend }",
    rejectContaining "throughgo requireth matching middle endpoints" "cannot unify" $
      compile "let bad ≔ (eftbend @ℤ @+1) throughgo (eftbend @ℤ @+2)"
  ]
  where
    compile source = compileWith library "is_test.tung" ("use is.tung\n" ++ source)

-- canonical finite sets prove their laws in identity, with no added assumptions.
setCases :: Library -> [Test]
setCases library =
  [ expectEq "finite set laws have no holes or axioms" (Right ()) do
      program <- compile laws
      audits <- traverse (Source.auditProof program) ["yoke_swap", "meet_swap", "yoke_associate", "distribute", "least", "same_sound"]
      mapM_ (Source.verifyProof program (Just [])) audits,
    expectEq "finite sets normalise order, repetition, and empty yokes" (Right (replicate 6 True)) do
      program <- compile values
      traverse
        (uncurry (sameNormalIn program))
        [ ("left", "right"),
          ("left to_list", "nay ‥ (yea ‥ list~empty)"),
          ("left ∨ right", "left"),
          ("left ∧ right", "left"),
          ("set~empty ∨ left", "left"),
          ("(left set~∖ (yea set~onesome)) to_list", "nay ‥ list~empty")
        ],
    rejectContaining "finite sets need a lawful element order" "order_whole" $
      compile "ilk token:* { only:token } let bad:token set ≔ set~empty",
    rejectContaining "the raw finite set constructor stayeth private" "unknown name 'ordered'" $
      compile "let bad ≔ list~empty ordered",
    rejectContaining "distinct finite sets cannot be proved identical" "cannot unify" $
      compile "let bad:(yea set~onesome) = (nay set~onesome) ≔ eftbend"
  ]
  where
    compile source = compileWith library "set_test.tung" (imports ++ "\n" ++ source)
    imports =
      """
      use ilk/set.tung
      use ilk/list.tung
      use ilk/two.tung
      use flock/hath_inhold.tung
      use flock/hath_same.tung
      use flock/order/order_whole.tung
      use flock/order/semilattice_lower.tung
      use flock/order/semilattice_upper.tung
      use flock/order/semilattice_upper_bounded.tung
      use flock/order/lattice_distributive.tung
      use flock/same_to_is.tung
      use is.tung
      """
    values =
      """
      let left ≔ (yea ‥ (nay ‥ (yea ‥ list~empty))) set~from_list
      let right ≔ (set~empty set~put nay) set~put yea
      """
    laws =
      """
      let yoke_swap:[@α:*, @:α order_whole, a:α set, b:α set, (a ∨ b) = (b ∨ a)] ≔ a ∨_swap b
      let meet_swap:[@α:*, @:α order_whole, a:α set, b:α set, (a ∧ b) = (b ∧ a)] ≔ a ∧_swap b
      let yoke_associate:[@α:*, @:α order_whole, a:α set, b:α set, c:α set, ((a ∨ b) ∨ c) = (a ∨ (b ∨ c))] ≔ a ∨_∨ b c
      let distribute:[@α:*, @:α order_whole, a:α set, b:α set, c:α set, (a ∧ (b ∨ c)) = ((a ∧ b) ∨ (a ∧ c))] ≔ a ∧_∨ b c
      let least:[@α:*, @:α order_whole, a:α set, (set~empty ∨ a) = a] ≔ a ⟂_∨
      let same_sound:[@α:*, @:α order_whole, a:α set, b:α set, (a ≍ b) = yea, a = b] ≔ a ≍_= b
      """

-- each ℕ host operation computeth natively on literals and unfoldeth its
-- structural model otherwise; the two must agree, and proofs may use the model.
numberCases :: Library -> [Test]
numberCases library =
  [ agreement "ℕ" (libraryModule library "ilk/natural.tung") ["is_same", "is_at_most", "eking", "offdrawing", "folding"] (0, 12) (show :: Int -> String),
    agreement "ℤ" (libraryModule library "ilk/wholetale.tung") ["is_same", "is_at_most", "eking", "offdrawing", "folding"] (-12, 12) signed,
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
      use flock/algebra/whole/hath_eke.tung
      use is.tung
      let right_naught: [n: ℕ, (n + 0) = n] ≔ eftbend
      let left_naught: [n: ℕ, (0 + n) = n] ≔
        match n {
          0 ^ eftbend,
          k heir ^ {x: ℕ ^ x heir} leibnitz (k left_naught)
        }
      """

-- the yoneda and yoneda_co round trips compute for `maybe`; yoneda's
-- transformation direction needeth naturality, yoneda_co's other direction
-- needeth quotients, and false round trips are rejected.
yonedaCases :: Library -> [Test]
yonedaCases library =
  [ expectEq "lifting a value and taking it back computeth to the value" (Right True) $
      compile "" >>= \program -> sameNormalIn program "((+3 some) lift) unlift" "+3 some",
    expectEq "a proved round trip computeth to eftbend" (Right ()) $
      () <$ compile "let back: (((+3 some) lift) unlift) = (+3 some) ≔ (+3 some) unlift_lift",
    rejectContaining "the transformation direction needeth a naturality proof" "cannot unify" $
      compile "let bad: [n: maybe yoneda ℤ, f: [ℤ, ℤ], (f ((n unlift) lift)) = (f n)] ≔ n lift_unlift eftbend f",
    rejectContaining "lifting doth not give the value under another function" "cannot unify" $
      compile "let bad: [a: ℤ maybe, ({x ^ x + +1} (a lift)) = a] ≔ a unlift_lift",
    expectEq "yoneda_co mappeth a type that hath no functor" (Right ()) $
      () <$ compileCo "ilk twice: [α: *, *] { twice_of: [α, α, α twice] }\nlet changed: twice yoneda_co string ≔ ((+1 twice_of +2) yoneda_co~lift) warp to_string",
    expectEq "yoneda_co unlifteth after composed changes" (Right True) $
      compileCo "let changed ≔ (((+1 some) yoneda_co~lift) warp {x ^ x + +1}) warp {x ^ x + +1}"
        >>= \program -> sameNormalIn program "changed yoneda_co~unlift" "+3 some",
    expectEq "a yoneda_co round trip computeth to the value" (Right True) $
      compileCo "" >>= \program -> sameNormalIn program "((+3 some) yoneda_co~lift) yoneda_co~unlift" "+3 some",
    rejectContaining "a yoneda_co is not the lift of its unlift without quotients" "cannot unify" $
      compileCo "let bad: [c: maybe yoneda_co ℤ, ((c yoneda_co~unlift) yoneda_co~lift) = c] ≔ eftbend"
  ]
  where
    compile source = compileWith library "yoneda_test.tung" ("use ilk/maybe.tung\nuse ground.tung\nuse yoneda.tung\n" ++ source)
    compileCo source = compileWith library "coyoneda_test.tung" ("use ilk/maybe.tung\nuse ground.tung\nuse yoneda_co.tung\n" ++ source)

-- the group theorems hold for signs under multiplication; a monoid whose
-- values lack inverses cannot be a group.
groupCases :: Library -> [Test]
groupCases library =
  [ expectEq "the inverse of a product computeth for a small group" (Right [True, True]) do
      program <- compile ""
      traverse
        (uncurry (sameNormalIn program))
        [("(minus · minus) /", "plus"), ("minus /· plus", "minus")],
    expectEq "group theorems apply to a concrete group" (Right ()) $
      () <$ compile "let twice: ((minus /) /) = minus ≔ minus /_/\nlet turned: ((plus · minus) /) = ((minus /) · (plus /)) ≔ plus /_over_· minus",
    expectEq "the homomorphism theorems apply to a concrete homomorphism" (Right ()) $
      () <$ compile "use flock/algebra/whole/group_likeshaper.tung\nlet trivial: [sign, sign] ≔ {_ ^ plus}\nlet hom: trivial likeshaped ≔ {_, _ ^ eftbend}\nlet sent: ((one: sign) trivial) = one ≔ trivial one_f hom\nlet same: (plus trivial) = (minus trivial) ≔ trivial kernel_fibre hom plus minus (trivial fibre_kernel hom plus minus eftbend)",
    rejectContaining "a map that turneth signs is no homomorphism" "cannot unify" $
      compile "use flock/algebra/whole/group_likeshaper.tung\nlet turn: [sign, sign] ≔ {plus ^ minus, minus ^ plus}\nlet bad: turn likeshaped ≔ {_, _ ^ eftbend}",
    rejectContaining "a value without an inverse maketh no group" "cannot unify" $
      compileWith library "group_test.tung" "use ground.tung\nuse is.tung\nuse flock/algebra/whole/group_fold.tung\nbizen: 𝟚 group_· { let /: [a:] ≔ a let ·_/ ≔ {yea ^ eftbend, nay ^ eftbend} let /_· ≔ {yea ^ eftbend, nay ^ eftbend} }"
  ]
  where
    compile source = compileWith library "group_test.tung" (sign ++ source)
    sign =
      """
      use flock/algebra/whole/group_fold.tung
      use flock/algebra/whole/hath_fold.tung
      use flock/algebra/whole/hath_one.tung
      use flock/algebra/whole/monoid_fold.tung
      use flock/algebra/whole/semigroup_fold.tung
      use is.tung
      ilk sign: * { plus: sign, minus: sign }
      bizen: sign hath_· { let · ≔ {plus, b ^ b, minus, plus ^ minus, minus, minus ^ plus} }
      bizen: sign hath_one { let one ≔ plus }
      bizen: sign semigroup_· { let ·_· ≔ {plus, _, _; minus, plus, _; minus, minus, plus; minus, minus, minus ^ eftbend} }
      bizen: sign monoid_· { let one_· ≔ {plus; minus ^ eftbend} let ·_one ≔ {plus; minus ^ eftbend} }
      bizen: sign group_· { let /: [a:] ≔ a let ·_/ ≔ {plus; minus ^ eftbend} let /_· ≔ {plus; minus ^ eftbend} }

      """

-- every ring is a module over itself; a module needeth a ring of scalars.
moduleCases :: Library -> [Test]
moduleCases library =
  [ expectEq "a ring acteth on itself by multiplication" (Right True) $
      compile "" >>= \program -> sameNormalIn program "+3 ∘ +4" "+12",
    expectEq "the module laws of a ring over itself are proved" (Right ()) $
      () <$ compile "let law: [r: ℤ, s: ℤ, a: ℤ, ((r · s) ∘ a) = (r ∘ (s ∘ a))] ≔ r ·_∘ s a",
    rejectContaining "floats are no ring of scalars" "no bizen" $
      compile "let bad: float ≔ 2.0 ∘ 3.0"
  ]
  where
    compile source = compileWith library "module_test.tung" ("use ground.tung\nuse flock/algebra/whole/module.tung\n" ++ source)

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
      use ilk/naught.tung
      let never: [_: ℕ, _: ℕ, *] ≔ 𝟘
      let founded: ℕ wellgrounded never ≔ {x ^ {y, impossible ^ impossible ({}: [𝟘, ℕ accessible never y])} access}
      let answer: ℕ ≔ founded wellgrounded_selfcall {x, _ ^ x heir} 3
      """

-- the list theorems are proved; false or ill-founded statements beside them
-- must be rejected for the stated reason, without `sorry`.
soundnessCases :: Library -> [Test]
soundnessCases library =
  [ expectEq "a closed instance of a proved setting computeth to eftbend" (Right True) do
      program <-
        compile
          """
          let closed: ((1 ‥ (2 ‥ empty)) eftwend $ eftwend) = (1 ‥ (2 ‥ empty)) ≔ (1 ‥ (2 ‥ empty)) eftwend_eftwend
          let direct: ((1 ‥ (2 ‥ empty)) eftwend $ eftwend) = (1 ‥ (2 ‥ empty)) ≔ eftbend
          """
      sameNormalIn program "closed" "direct",
    rejectContaining "a list is not its own double" "cannot unify" $
      compile "let bad: [l: ℕ list, (l · l) = l] ≔ eftbend",
    rejectContaining "athanging is not commutative" "cannot unify" $
      compile "let bad: [a: ℕ list, b: ℕ list, (a · b) = (b · a)] ≔ match a { empty ^ (b ·_empty) evenmete, first ‥ rest ^ (first ‥) leibnitz (rest bad b) }",
    rejectContaining "distinct lists are not same" "cannot unify 1 with 2" $
      compile "let bad: (1 ‥ empty) = (2 ‥ empty) ≔ eftbend",
    rejectContaining "reversing is not the sameness" "cannot unify" $
      compile "let bad: [l: ℕ list, (l eftwend) = l] ≔ match l { empty ^ eftbend, first ‥ rest ^ (first ‥) leibnitz (rest bad) }",
    rejectContaining "selfcalling on the same list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ l bad",
    rejectContaining "selfcalling on a larger list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ (0 ‥ l) bad",
    rejectContaining "a half match proveth nothing" "the match is not exhaustive: missing ‥" $
      compile "let bad: [l: ℕ list, l = empty] ≔ match l { empty ^ eftbend }",
    rejectContaining "an empty function needeth an impossible input" "the match is not exhaustive" $
      compile "let bad: [(1 ‥ empty) = (1 ‥ empty), 𝟘] ≔ {}",
    rejectContaining "pointwise same functions are not provably same" "cannot unify" $
      compile "let bad: [f: [ℕ, ℕ], g: [ℕ, ℕ], [n: ℕ, (n f) = (n g)], f = g] ≔ {_ ^ eftbend}",
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
            "use flock/algebra/whole/hath_fold.tung",
            "use ilk/list.tung",
            "use ilk/list_setting.tung",
            "use ilk/natural.tung",
            "use ilk/two.tung",
            "use ilk/naught.tung"
          ]
          ++ source

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
        ++ "let echo:𝟙 deed ≔ read bind { _ ^ >{then, 'a' write_line, random, 0 sleep, only sheer} } "
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
                  then Just "host catalogue inholdeth an argumentless binding that is not a deed"
                  else Nothing
  where
    argumentless HostSignature {hostArguments, hostResult} = null hostArguments && not (isDeed hostResult)
    isDeed (HostApp "deed" _) = True
    isDeed _ = False
    foreignNames = \case
      Source.ShownDeclaration declaration -> foreignNames declaration
      Source.HostDeclaration {Source.hostKey} -> [hostKey]
      _ -> []

oneDataTypeCase :: [FilePath] -> Test
oneDataTypeCase paths = listToMaybe . catMaybes <$> traverse checkModule paths
  where
    checkModule path = do
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
          [name] | asciiName name == takeBaseName path -> Nothing
          [name] -> Just (path ++ " defineth class '" ++ name ++ "'")
          _ -> Just (path ++ " owneth " ++ show (length names) ++ " classes")
      | null names = Nothing
      | otherwise = Just (path ++ " defineth a class outside the flock directory")
    classPrefix = "flock/"
    -- module paths keep the documented ascii spellings of symbolic terms.
    asciiName = concatMap (\character -> maybe [character] id (lookup character spellings))
    spellings = [('+', "eke"), ('-', "offdraw"), ('÷', "deal"), ('%', "deal_leftover"), ('·', "fold"), ('≤', "at_most"), ('≍', "same"), ('=', "is"), ('∋', "inhold"), ('‖', "length")]

classNames :: Source.Declaration -> [String]
classNames (Source.FlockDeclaration name _ _) = [name]
classNames (Source.ShownDeclaration declaration) = classNames declaration
classNames _ = []
