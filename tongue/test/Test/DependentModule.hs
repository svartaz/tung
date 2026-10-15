-- dependent modules: `use`, `show`, qualification, ambiguity, and cycles.
module Test.DependentModule (group) where

import Data.List (intercalate, sortOn)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject, compileProjectDetailed, compileProjectWith)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung (SourceSpan (..))
import Tung.Dependent
import Tung.Dependent.Source (CompileFailure (..), DependencyKind (..), FailureKind (..), ProofDependency (..), SourceProgram, auditDependencies, auditProof, parseSource, sourceNames, typeOfName, verifyProof)

group :: IO Harness.Group
group = do
  files <- traverse (\name -> (name,) <$> exampleSource ("modules/" ++ name)) ["host.tung", "kindful.tung", "main.tung"]
  library <- loadLibrary ["_fremmed.tung", "ilk/one.tung"]
  Harness.group "dependent-module" (exampleRun library files : replacedFixture library : resolvedNames : tests ++ mutualModuleTests ++ proofAuditTests ++ cachedTests ++ map generatedGraph graphs)

-- the example's main useth bare and qualified imports, imported recursion, and
-- bookhoard modules.
exampleRun :: Library -> [(String, String)] -> Test
exampleRun library files = expectEq "a multi-module forewrit runneth" (Right (Right 0, "tung tung tung tung \n")) do
  main <- maybe (Left "missing main.tung") Right (lookup "main.tung" files)
  program <- compileWith (withModules files library) "main.tung" main
  runSimulated program []

-- each written global, with its span: bare and qualified names, constructors
-- in patterns, a call, and a field read by its receiver's ilk. locals and
-- binders are not globals.
resolvedNames :: Test
resolvedNames =
  expectEq
    "checking recordeth the global each written name resolveth to, and whether it nameth an ilk"
    ( Right
        [ ("two", "dep.tung", "two", True),
          ("two", "dep.tung", "two", True),
          ("yea", "dep.tung", "yea", False),
          ("nay", "dep.tung", "nay", False),
          ("nay", "dep.tung", "nay", False),
          ("d~yea", "dep.tung", "yea", False),
          ("pair", "dep.tung", "pair", True),
          ("two", "dep.tung", "two", True),
          ("left", "dep.tung", "pair.left", False),
          ("flip", "main.tung", "flip", False)
        ]
    )
    do
      program <- compileProject (SourceModule "main.tung") source (Map.fromList [("dep.tung", dependency)])
      pure [(slice span, path, name, ilk) | (span, SymbolId (SourceModule path) name, ilk) <- sortOn (\(span, _, _) -> spanStart span) (sourceNames program)]
  where
    dependency = "show ilk two: * { yea: two, nay: two }\nshow ilk pair: * { pair_of: [left: two, right: two, pair] }\n"
    source = "bring dep.tung d\nlet flip: [two, two] ≔ {yea ^ nay, nay ^ d~yea}\nlet first: [p: pair, two] ≔ p.left flip\n"
    slice (SourceSpan start end) = take (end - start) (drop start source)

replacedFixture :: Library -> Test
replacedFixture library =
  rejectContaining "a replaced fixture cannot retain a cached constructor" "unknown name 'only'" $
    compileWith
      (withModules [("ilk/one.tung", "show ilk 𝟙:* {}\n")] library)
      "replaced_fixture.tung"
      """
      bring ilk/one.tung
      let worth:𝟙 ≔ only

      """

tests :: [Test]
tests =
  [ expectEq "shown names are visible bare and qualified" (Right True) $
      checked "bring bool.tung\nlet a:bool ≔ yes\nlet b:bool~bool ≔ bool~no\n" [bool],
    expectEq "an alias replaceth the default namespace" (Right True) $
      checked "bring bool.tung truth\nlet a:truth~bool ≔ truth~yes\n" [bool],
    rejectContaining "the default namespace is gone after an alias" "unknown name 'bool~yes'" $
      compile "bring bool.tung truth\nlet a ≔ bool~yes\n" [bool],
    rejectContaining "unshown names stay private" "unknown name 'secret'" $
      compile "bring bool.tung\nlet a ≔ secret\n" [bool],
    rejectContaining "a bare name shown by two modules is ambiguous" "ambiguous name 'yes'" $
      compile "bring bool.tung\nbring other.tung\nlet a ≔ yes\n" [bool, other],
    rejectContaining "re-export ambiguity nameth visible aliases" "right~yes and left~yes" $
      compile "bring first.tung left\nbring second.tung right\nlet a ≔ yes" [bool, other, ("first.tung", "bring bool.tung show bool~yes"), ("second.tung", "bring other.tung show other~yes")],
    expectEq "qualification resolveth an ambiguous name" (Right True) $
      checked "bring bool.tung\nbring other.tung\nlet a:bool~bool ≔ bool~yes\n" [bool, other],
    expectEq "a local definition shadoweth a bare import" (Right True) $
      checked "bring bool.tung\nilk mine:* { yes: mine }\nlet a:mine ≔ yes\n" [bool],
    rejectContaining "local names still cannot repeat" "top-level name repeateth" $
      compile "let a ≔ *\nlet a ≔ *\n" [],
    expectEq "one module imported twice keepeth one sameness" (Right True) $
      checked "bring bool.tung\nbring wrap.tung\nlet a:bool ≔ yes keep\n" [bool, ("wrap.tung", "bring bool.tung\nshow let keep:[bool, bool] ≔ {x ^ x}\n")],
    expectEq "a forward assumption is scheduled before its users" (Right True) $
      checked (equalitySource ++ "let soothed:[x:T,x = x] ≔ eftbend\norsetting T:*") [],
    expectEq "later lambda annotations seeth earlier binders" (Right True) do
      program <- compile "let shadow ≔ sameness\nlet sameness ≔ {shadow:*, x:shadow ^ x}" []
      sameNormalIn program "* shadow *" "*",
    expectEq "a later local let doth not hide an earlier global use" (Right True) do
      program <- compile "let before ≔ (let x ≔ later let later ≔ +0 yield x)\nlet later ≔ +1" []
      sameNormalIn program "before" "+1",
    expectEq "a bizen may precede a helper that useth its flock at another type" (Right True) $
      checked "flock keeps: [α: *, *] { let keep: [α, α] }\nilk a: * { x: a }\nilk b: * { y: b }\nbizen: b keeps { let keep ≔ helper }\nlet helper: [b, b] ≔ {v ^ match x keep { x ^ v }}\nbizen: a keeps { let keep: [v:] ≔ v }\n" [],
    expectEq "an ambiguous name that is no constructor still bindeth a recursive input" (Right True) $
      checked "bring a.tung\nbring b.tung\nilk nat:* { z: nat, s: [nat, nat] }\nlet rime: [n: nat, same: nat, nat] ≔ match n { z ^ same, m s ^ m rime same }\n" [("a.tung", "show let same ≔ *\n"), ("b.tung", "show let same ≔ *\n")],
    rejectContaining "an ambiguous constructor in a pattern is rejected" "ambiguous name 'yes'" $
      compile "bring bool.tung\nbring other.tung\nlet pick: [bool, bool] ≔ { yes ^ no, x ^ x }\n" [bool, other],
    rejectContaining "a use cycle is rejected" "bring cycle: a.tung -> b.tung -> a.tung" $
      compile "bring a.tung\n" [("a.tung", "bring b.tung\n"), ("b.tung", "bring a.tung\n")],
    rejectContaining "a missing module is reported" "missing bring" $
      compile "bring missing.tung\n" [],
    rejectContaining "errors name the module" "in bring 'broken.tung'" $
      compile "bring broken.tung\n" [("broken.tung", "let bad ≔ unknown\n")],
    rejectContaining "show precedeth a declaration" "show must precede" $
      parseSource "show bring bool.tung\n",
    rejectContaining "use sameness top-level" "bring and show must be top-level" $
      parseSource "let a ≔ (bring bool.tung yield *)\n"
  ]
  where
    bool = ("bool.tung", "show ilk bool:* { no: bool, yes: bool }\nlet secret ≔ *\n")
    other = ("other.tung", "show ilk answer:* { yes: answer }\n")

mutualModuleTests :: [Test]
mutualModuleTests =
  [ expectEq "shown mutual families retain their own constructors and imported matches" (Right True) do
      program <- compile "bring mutual.tung" [mutual]
      sameNormalIn program "mutual~sample parent" "naught_even",
    rejectContaining "an unshown sibling family remaineth private" "unknown name 'odd'" $
      compile "bring mutual.tung\nlet bad ≔ odd" [mutual],
    expectEq "declaration cycle diagnostics retain the first name's span" (Right expected) $
      case compileProjectDetailed Map.empty (SourceModule "cycle.tung") "let a:* ≔ b\nlet b:* ≔ a" Map.empty of
        Left failure -> Right failure
        Right _ -> Left "accepted a declaration cycle"
  ]
    ++ [ rejectContaining label "declaration cycle" (compile source [])
       | (label, source) <-
           [ ("a type alias cannot yoke an inductive cycle", "ilk a:* { make:[t, a] }\nlet t:* ≔ a"),
             ("a flock cannot yoke an inductive cycle", "ilk a:* { make:[a c, a] }\nflock c:[α:*, *] { let witness:a }")
           ]
       ]
  where
    expected = CompileFailure CheckFailure Nothing (Just (SourceSpan 4 5)) "declaration cycle: a -> b"
    mutual =
      ( "mutual.tung",
        """
        show ilk even:* { naught_even:even, from_odd:[odd, even] }
        ilk odd:* { from_even:[even, odd] }
        show let sample:even ≔ (naught_even from_even) from_odd
        show let parent:[even, even] ≔ {
          naught_even ^ naught_even,
          o from_odd ^ match o { e from_even ^ e }
        }

        """
      )

proofAuditTests :: [Test]
proofAuditTests =
  [ expectEq "proof auditing followeth imported private and re-exported axioms" (Right expected) do
      program <- base
      audited <- auditProof program "soothed"
      pure (sortOn fst [(dependencySymbol, dependencyKind) | ProofDependency {..} <- auditDependencies audited]),
    expectEq "an axiom policy resolveth a re-export by its visible alias" (Right ()) do
      program <- base
      auditProof program "public_soothing" >>= verifyProof program True (Just ["shared~visible"]),
    reject "allowing a re-exported axiom doth not allow a private dependency" do
      program <- base
      auditProof program "soothed" >>= verifyProof program True (Just ["shared~visible"])
  ]
  where
    base = compile source modules
    expected = sortOn fst [(SymbolId (SourceModule "base.tung") name, AxiomDependency) | name <- ["hidden", "visible"]]
    source =
      """
      bring forward.tung shared
      let soothed:ℕ ≔ shared~visible shared~exposed
      let public_soothing:ℕ ≔ shared~visible
      """
    modules =
      [ ( "base.tung",
          """
          orsetting hidden:ℕ
          show orsetting visible:ℕ
          orsetting unused:ℕ
          let helper:ℕ ≔ hidden
          show let exposed:[ℕ,ℕ] ≔ {_ ^ helper}
          """
        ),
        ("forward.tung", "bring base.tung source\nshow source~exposed\nshow source~visible")
      ]

cachedTests :: [Test]
cachedTests =
  [ expectEq "conflicting cached dependencies cannot prove an empty type" (Right expected) do
      cached <- cache "show ilk tag:* {}" "show ilk empty:* {} show let explode:[tag,empty] ≔ {}"
      case compileProjectDetailed cached RootModule "bring a.tung\nbring b.tung\nlet impossible:b~empty ≔ a~worth b~explode" Map.empty of
        Left failure -> Right failure
        Right _ -> Left "accepted conflicting cached dependencies",
    expectEq "an identical cached diamond keepeth its checked identities" (Right True) do
      cached <- cache inhabited "show let keep:[tag,tag] ≔ {x ^ x}"
      program <- compileProjectWith cached RootModule "bring a.tung\nbring b.tung\nlet answer ≔ a~worth b~keep" Map.empty
      sameNormalIn program "answer" "a~worth"
  ]
  where
    expected = CompileFailure CheckFailure Nothing (Just (SourceSpan 19 20)) "conflicting definition of 'tag' in bring 'b.tung'"
    inhabited = "show ilk tag:* { only:tag }"
    cache dependency source = do
      left <- compileProject (SourceModule "a.tung") "bring dep.tung show let worth:tag ≔ only" (Map.singleton "dep.tung" inhabited)
      right <- compileProject (SourceModule "b.tung") ("bring dep.tung " ++ source) (Map.singleton "dep.tung" dependency)
      pure (Map.fromList [("a.tung", left), ("b.tung", right)])

compile :: String -> [(String, String)] -> Either String SourceProgram
compile source modules = compileProject (SourceModule "root.tung") source (Map.fromList modules)

checked :: String -> [(String, String)] -> Either String Bool
checked source modules = True <$ compile source modules

-- every acyclic import graph over three modules, as the edges `(importer,
-- imported)` with the importer later.
graphs :: [[(Int, Int)]]
graphs = foldr (\edge rest -> rest ++ map (edge :) rest) [[]] [(1, 0), (2, 0), (2, 1)]

-- each module declareth an ilk, a flock and its bizen, a shown worth, a
-- private name every module shareth, and a qualified re-export of each
-- import's worth. the root useth every module. declarations and imports are
-- written forward and reversed; every qualified chain must still normalise
-- to its source, and the root's types must render alike.
generatedGraph :: [(Int, Int)] -> Test
generatedGraph edges = expectEq ("generated module graph " ++ show edges) (Right True) do
  -- rendered types name modules by the root's namespaces, so orderings are
  -- compared within one aliasing.
  outcomes <- traverse (\aliased -> traverse build [(declarations, imports, aliased) | declarations <- [id, reverse], imports <- [id, reverse]]) [False, True]
  if all agree outcomes then Right True else Left ("orderings disagree: " ++ show outcomes)
  where
    name index = "m" ++ show index
    path index = name index ++ ".tung"
    imported index = [target | (importer, target) <- edges, importer == index]
    module' order index =
      let declarations =
            [ "show ilk t" ++ show index ++ ": * { c" ++ show index ++ ": t" ++ show index ++ " }",
              "show flock h" ++ show index ++ ": [α: *, *] { let pick" ++ show index ++ ": [α, α] }",
              "bizen: t" ++ show index ++ " h" ++ show index ++ " { let pick" ++ show index ++ ": [x:] ≔ x }",
              "show let v" ++ show index ++ ": t" ++ show index ++ " ≔ c" ++ show index ++ " pick" ++ show index,
              "let secret ≔ *"
            ]
              ++ ["show let r" ++ show target ++ ": " ++ name target ++ "~t" ++ show target ++ " ≔ " ++ name target ++ "~v" ++ show target | target <- imported index]
       in intercalate "\n" (["bring " ++ path target | target <- imported index] ++ order declarations)
    agree = \case
      first : rest -> all (== first) rest
      [] -> True
    -- an aliased root nameth each module by another namespace.
    space aliased index = if aliased then "a" ++ show index else name index
    build (declarationOrder, importOrder, aliased) = do
      let modules = [(path index, module' declarationOrder index) | index <- [0 .. 2]]
          worth index = space aliased index ++ "~v" ++ show index
          root = intercalate "\n" (importOrder ["bring " ++ path index ++ (if aliased then " " ++ space aliased index else "") | index <- [0 .. 2]] ++ ["let answer ≔ (" ++ worth 0 ++ " both " ++ worth 1 ++ ") both " ++ worth 2])
          chains = [(space aliased importer ++ "~r" ++ show target, space aliased target ++ "~v" ++ show target) | (importer, target) <- edges]
      program <- compile (root ++ "\nilk pair: [α: *, β: *, *] { both: [α, β, α pair β] }") modules
      same <- traverse (uncurry (sameNormalIn program)) chains
      if and same then traverse (typeOfName program) ["answer"] else Left ("a re-export lost its identity in " ++ show edges)
