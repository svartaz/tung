-- library registry, dependency, ownership, export, and type-checking invariants.
-- the graph must be acyclic, dependencies may not import ground, and each source
-- owneth at most one algebraic data declaration.
module Test.Standard (group) where

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
  Harness.group "standard" $
    registry
      : loaded
      : noUmbrellaDependencyCase files
      : groundEffectExportsCase imports
      : systemExplicitCase imports
      : runnerEffectsCase imports
      : primitiveCatalogueCase imports
      : classLayoutCase files
      : equalityCases library
      ++ soundnessCases library
      ++ groundedCases library
      ++ yonedaCases library
      ++ topologyCases library
      ++ lawCases library
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
        (\expression -> sameNormalIn program expression "reflect @ℤ @+1")
        [ "same leibnitz (reflect @ℤ @+1)",
          "(reflect @ℤ @+1) symmetry",
          "(reflect @ℤ @+1) transit (reflect @ℤ @+1)"
        ],
    expectEq "library identity supporteth arbitrary types and dependent throughbear" (Right ()) $
      ()
        <$ compile
          """
          let reflect_value:[@α:*, x:α, x = x] ≔ reflect
          let reflect_type:[@α:*, α = α] ≔ reflect
          let shift_type:[@α:*, @β:*, reflect:α = β, α, β] ≔ {x ^ x}
          let shift_value:[@α:*, @a:α, @b:α, @P:[α,*], p:a = b, value:a P, b P] ≔ p throughbear value
          """,
    rejectContaining "library identity doth not provide axiom K" "axiom K" $
      compile "let k:[@α:*, @a:α, p:a = a, p = reflect] ≔ match p { reflect ^ reflect }",
    rejectContaining "transit requireth matching middle endpoints" "cannot unify" $
      compile "let bad ≔ (reflect @ℤ @+1) transit (reflect @ℤ @+2)"
  ]
  where
    compile source = compileWith library "is_test.tung" ("bring is.tung\n" ++ source)

-- canonical finite sets prove their laws in identity, with no added assumptions.
setCases :: Library -> [Test]
setCases library =
  [ expectEq "finite set laws have no holes or axioms" (Right ()) do
      program <- compile laws
      audits <- traverse (Source.auditProof program) ["join_swap", "meet_swap", "join_associate", "distribute", "least", "equal_sound"]
      mapM_ (Source.verifyProof program True (Just [])) audits,
    expectEq "finite sets normalise order, repetition, and empty joins" (Right (replicate 6 True)) do
      program <- compile values
      traverse
        (uncurry (sameNormalIn program))
        [ ("left", "right"),
          ("left to_list", "nay ‥ (yea ‥ list~empty)"),
          ("left ⋎ right", "left"),
          ("left ⋏ right", "left"),
          ("set~empty ⋎ left", "left"),
          ("(left set~∖ (yea set~onesome)) to_list", "nay ‥ list~empty")
        ],
    rejectContaining "finite sets need a lawful element order" "order_total" $
      compile "type token:* { only:token } let bad:token set ≔ set~empty",
    rejectContaining "the raw finite set constructor stayeth private" "unknown name 'ordered'" $
      compile "let bad ≔ list~empty ordered",
    rejectContaining "distinct finite sets cannot be proved identical" "cannot unify" $
      compile "let bad:(yea set~onesome) = (nay set~onesome) ≔ reflect"
  ]
  where
    compile source = compileWith library "set_test.tung" (imports ++ "\n" ++ source)
    imports =
      """
      bring type/set.tung
      bring type/list.tung
      bring type/two.tung
      bring class/hath_inhold.tung
      bring class/hath_equal.tung
      bring class/order/order_total.tung
      bring class/order/semilattice_lower.tung
      bring class/order/semilattice_upper.tung
      bring class/order/semilattice_upper_bounded.tung
      bring class/order/lattice_distributive.tung
      bring class/equal_to_is.tung
      bring is.tung
      """
    values =
      """
      let left ≔ (yea ‥ (nay ‥ (yea ‥ list~empty))) set~from_list
      let right ≔ (set~empty set~put nay) set~put yea
      """
    laws =
      """
      let join_swap:[@α:*, @:α order_total, a:α set, b:α set, (a ⋎ b) = (b ⋎ a)] ≔ a ⋎_swap b
      let meet_swap:[@α:*, @:α order_total, a:α set, b:α set, (a ⋏ b) = (b ⋏ a)] ≔ a ⋏_swap b
      let join_associate:[@α:*, @:α order_total, a:α set, b:α set, c:α set, ((a ⋎ b) ⋎ c) = (a ⋎ (b ⋎ c))] ≔ a ⋎_⋎ b c
      let distribute:[@α:*, @:α order_total, a:α set, b:α set, c:α set, (a ⋏ (b ⋎ c)) = ((a ⋏ b) ⋎ (a ⋏ c))] ≔ a ⋏_⋎ b c
      let least:[@α:*, @:α order_total, a:α set, (set~empty ⋎ a) = a] ≔ a ⟂_⋎
      let equal_sound:[@α:*, @:α order_total, a:α set, b:α set, (a ≍ b) = yea, a = b] ≔ a ≍_= b
      """

-- each ℕ host operation computeth natively on literals and unfoldeth its
-- structural model otherwise; the two must agree, and proofs may use the model.
numberCases :: Library -> [Test]
numberCases library =
  [ agreement "ℕ" (libraryModule library "type/natural.tung") ["equal", "at_most", "add", "subtract", "multiply", "divide_leftover"] (0, 12) (show :: Int -> String),
    agreement "ℤ" (libraryModule library "type/integer.tung") ["equal", "at_most", "add", "subtract", "multiply", "divide_leftover"] (-12, 12) signed,
    agreement "unicode" (libraryModule library "type/unicode.tung") ["equal", "at_most"] (0, 3) (\index -> ['`', characters !! index]),
    agreement "string" (libraryModule library "type/string/building.tung") ["equal_string", "at_most_string", "join_string"] (0, 40) (\index -> "'" ++ spelled index ++ "'"),
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
    -- scalars from several planes, so code-point order is exercised.
    characters = "zλ😀a"
    spelled 0 = ""
    spelled index = characters !! ((index - 1) `mod` 4) : spelled ((index - 1) `div` 4)
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
      bring type/natural.tung
      bring class/algebra/total/hath_add.tung
      bring is.tung
      let right_zero: [n: ℕ, (n + 0) = n] ≔ reflect
      let left_zero: [n: ℕ, (0 + n) = n] ≔
        match n {
          0 ^ reflect,
          k next ^ {x: ℕ ^ x next} leibnitz (k left_zero)
        }
      """

-- the yoneda and yoneda_co round trips compute for `optional`; yoneda's
-- transformation direction needeth naturality, yoneda_co's other direction
-- needeth quotients, and false round trips are rejected.
yonedaCases :: Library -> [Test]
yonedaCases library =
  [ expectEq "lifting a value and taking it back computeth to the value" (Right True) $
      compile "" >>= \program -> sameNormalIn program "((+3 some) lift) unlift" "+3 some",
    expectEq "a proved round trip computeth to reflect" (Right ()) $
      () <$ compile "let back: (((+3 some) lift) unlift) = (+3 some) ≔ (+3 some) unlift_lift",
    rejectContaining "the transformation direction needeth a naturality proof" "cannot unify" $
      compile "let bad: [n: optional yoneda ℤ, f: [ℤ, ℤ], (f ((n unlift) lift)) = (f n)] ≔ n lift_unlift reflect f",
    rejectContaining "lifting doth not give the value under another function" "cannot unify" $
      compile "let bad: [a: ℤ optional, ({x ^ x + +1} (a lift)) = a] ≔ a unlift_lift",
    expectEq "yoneda_co mappeth a type that hath no functor" (Right ()) $
      () <$ compileCo "type twice: [α: *, *] { twice_of: [α, α, α twice] }\nlet changed: twice yoneda_co string ≔ ((+1 twice_of +2) yoneda_co~lift) map to_string",
    expectEq "yoneda_co unlifteth after composed changes" (Right True) $
      compileCo "let changed ≔ (((+1 some) yoneda_co~lift) map {x ^ x + +1}) map {x ^ x + +1}"
        >>= \program -> sameNormalIn program "changed yoneda_co~unlift" "+3 some",
    expectEq "a yoneda_co round trip computeth to the value" (Right True) $
      compileCo "" >>= \program -> sameNormalIn program "((+3 some) yoneda_co~lift) yoneda_co~unlift" "+3 some",
    rejectContaining "a yoneda_co is not the lift of its unlift without quotients" "cannot unify" $
      compileCo "let bad: [c: optional yoneda_co ℤ, ((c yoneda_co~unlift) yoneda_co~lift) = c] ≔ reflect"
  ]
  where
    compile source = compileWith library "yoneda_test.tung" ("bring type/optional.tung\nbring often.tung\nbring yoneda.tung\n" ++ source)
    compileCo source = compileWith library "coyoneda_test.tung" ("bring type/optional.tung\nbring often.tung\nbring yoneda_co.tung\n" ++ source)

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
      () <$ compile "bring group_homomorphism.tung\nlet trivial: [sign, sign] ≔ {_ ^ plus}\nlet hom: trivial homomorphic ≔ {_, _ ^ reflect}\nlet sent: ((one: sign) trivial) = one ≔ trivial one_f hom\nlet same: (plus trivial) = (minus trivial) ≔ trivial kernel_fibre hom plus minus (trivial fibre_kernel hom plus minus reflect)",
    rejectContaining "a map that turneth signs is no homomorphism" "cannot unify" $
      compile "bring group_homomorphism.tung\nlet turn: [sign, sign] ≔ {plus ^ minus, minus ^ plus}\nlet bad: turn homomorphic ≔ {_, _ ^ reflect}",
    rejectContaining "a value without an inverse maketh no group" "cannot unify" $
      compileWith library "group_test.tung" "bring often.tung\nbring is.tung\nbring class/algebra/total/group_multiply.tung\nbizen: 𝟚 group_· { let /: [a:] ≔ a let ·_/ ≔ {yea ^ reflect, nay ^ reflect} let /_· ≔ {yea ^ reflect, nay ^ reflect} }"
  ]
  where
    compile source = compileWith library "group_test.tung" (sign ++ source)
    sign =
      """
      bring class/algebra/total/group_multiply.tung
      bring class/algebra/total/hath_multiply.tung
      bring class/algebra/total/hath_one.tung
      bring class/algebra/total/monoid_multiply.tung
      bring class/algebra/total/semigroup_multiply.tung
      bring is.tung
      type sign: * { plus: sign, minus: sign }
      bizen: sign hath_· { let · ≔ {plus, b ^ b, minus, plus ^ minus, minus, minus ^ plus} }
      bizen: sign hath_one { let one ≔ plus }
      bizen: sign semigroup_· { let ·_· ≔ {plus, _, _; minus, plus, _; minus, minus, plus; minus, minus, minus ^ reflect} }
      bizen: sign monoid_· { let one_· ≔ {plus; minus ^ reflect} let ·_one ≔ {plus; minus ^ reflect} }
      bizen: sign group_· { let /: [a:] ≔ a let ·_/ ≔ {plus; minus ^ reflect} let /_· ≔ {plus; minus ^ reflect} }

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
    compile source = compileWith library "module_test.tung" ("bring often.tung\nbring class/algebra/total/module.tung\n" ++ source)

-- a relation with nothing smaller is well-founded, and recursion on it runneth
-- the step once.
-- the discrete topology satisfieth every law, so every function out of it is
-- continuous, also after another; a bizen whose whole part is not open is rejected.
-- lying under goeth through meets, but a part lieth not under its meet.
topologyCases :: Library -> [Test]
topologyCases library =
  [ expectEq "the discrete topology maketh every function continuous" (Right ()) $
      () <$ compile discrete,
    rejectContaining "a topology must open the whole part" "cannot unify one~𝟙 with zero~𝟘" $
      compile
        """
        type point: * { lone: point }
        bizen: point topology {
          let open: [_:] ≔ 𝟘
          let whole_open ≔ only
          let empty_open ≔ only
          let meet_open: [_:, _:, _:, _:] ≔ only
          let join_open: [_:, _:] ≔ only
        }
        """,
    expectEq "lying under goeth through meets" (Right ()) $
      ()
        <$ compile
          """
          let left_twice: [@α: *, u: [α, *], v: [α, *], w: [α, *], ((u meet v) meet w) subset u]
            ≔ ((u meet v) meet w) subset_transit (u meet v) u ((u meet v) meet_subset_former w) (u meet_subset_former v)
          """,
    rejectContaining "a part lieth not under its meet" "cannot unify" $
      compile "let bad: [@α: *, u: [α, *], v: [α, *], u subset (u meet v)] ≔ {_, held ^ held}"
  ]
  where
    compile source = compileWith library "topology_test.tung" (imports ++ "\n" ++ source)
    imports =
      """
      bring class/algebra/partial/semigroupoid.tung
      bring class/topology.tung
      bring type/zero.tung
      bring type/one.tung
      """
    discrete =
      """
      type discrete: [α: *, *] { lay: [α, α discrete] }
      bizen: [@α: *, (α discrete) topology] {
        let open: [_:] ≔ 𝟙
        let whole_open ≔ only
        let empty_open ≔ only
        let meet_open: [_:, _:, _:, _:] ≔ only
        let join_open: [_:, _:] ≔ only
      }
      let discrete_continuous: [@α: *, @β: *, @: β topology, f: [α discrete, β], f continuous] ≔ {_, _ ^ only}
      let both: [@α: *, @β: *, @γ: *, @: γ topology, f: [α discrete, β discrete], g: [β discrete, γ], (f ▷ g) continuous]
        ≔ f ▷_continuous g (f discrete_continuous) (g discrete_continuous)
      """

-- class laws must rule out lax bizens: euclidean division yieldeth an outcome
-- for every divisor but zero, and a partial order is antisymmetry in `=`, so
-- a preorder with an equality that holdeth everywhere is not one.
lawCases :: Library -> [Test]
lawCases library =
  [ expectEq "dividing by a divisor other than zero yieldeth an outcome" (Right ()) $
      ()
        <$ compileWith
          library
          "euclidean_test.tung"
          """
          bring class/algebra/total/euclidean.tung
          bring class/algebra/total/hath_divide_leftover.tung
          bring type/optional.tung
          bring type/two.tung
          bring type/integer.tung
          bring is.tung
          let divided: ((+7 % -2) is_some) = yea ≔ +7 %_some -2 {k ^ match k {}}
          """,
    rejectContaining "an empty vector hath no head" "cannot unify" $
      compileWith library "vector_test.tung" "bring type/vector.tung m\nlet bad: ℤ ≔ m~empty m~head",
    rejectContaining "a lax identity maketh no partial order" "cannot unify" $
      compileWith
        library
        "partial_order_test.tung"
        """
        bring class/hath_equal.tung
        bring class/order/hath_at_most.tung
        bring class/order/order_partial.tung
        bring type/two.tung
        bring is.tung
        type rank: * { lesser: rank, greater: rank }
        bizen: rank hath_≍ { let ≍ ≔ {_, _ ^ yea} }
        bizen: rank order_partial {
          let ≤ ≔ {_, _ ^ yea}
          let ≤_reflect ≔ {_ ^ reflect}
          let ≤_antisymmetry ≔ {_, _ ^ reflect}
          let ≤_transit ≔ {_, _, _ ^ reflect}
          let ≤_= ≔ {_, _, _, _ ^ reflect}
        }
        """
  ]

groundedCases :: Library -> [Test]
groundedCases library =
  [ expectEq "well-founded recursion computeth its step" (Right True) do
      program <- compileWith library "grounded_test.tung" source
      sameNormalIn program "answer" "4"
  ]
  where
    source =
      """
      bring type/grounded.tung
      bring type/zero.tung
      let never: [_: ℕ, _: ℕ, *] ≔ 𝟘
      let founded: ℕ wellfounded never ≔ {x ^ {y, impossible ^ impossible ({}: [𝟘, ℕ grounded never y])} ground}
      let answer: ℕ ≔ founded wellfounded_recur {x, _ ^ x next} 3
      """

-- the list theorems are proved; false or ill-founded statements beside them
-- must be rejected for the stated reason, without `sorry`.
soundnessCases :: Library -> [Test]
soundnessCases library =
  [ expectEq "a closed instance of a proved theorem computeth to reflect" (Right True) do
      program <-
        compile
          """
          let closed: ((1 ‥ (2 ‥ empty)) eftwend $ eftwend) = (1 ‥ (2 ‥ empty)) ≔ (1 ‥ (2 ‥ empty)) eftwend_eftwend
          let direct: ((1 ‥ (2 ‥ empty)) eftwend $ eftwend) = (1 ‥ (2 ‥ empty)) ≔ reflect
          """
      sameNormalIn program "closed" "direct",
    rejectContaining "a list is not its own double" "cannot unify" $
      compile "let bad: [l: ℕ list, (l · l) = l] ≔ reflect",
    rejectContaining "appending is not commutative" "cannot unify" $
      compile "let bad: [a: ℕ list, b: ℕ list, (a · b) = (b · a)] ≔ match a { empty ^ (b ·_empty) symmetry, first ‥ leftover ^ (first ‥) leibnitz (leftover bad b) }",
    rejectContaining "distinct lists are not same" "cannot unify 1 with 2" $
      compile "let bad: (1 ‥ empty) = (2 ‥ empty) ≔ reflect",
    rejectContaining "reversing is not the identity" "cannot unify" $
      compile "let bad: [l: ℕ list, (l eftwend) = l] ≔ match l { empty ^ reflect, first ‥ leftover ^ (first ‥) leibnitz (leftover bad) }",
    rejectContaining "recursion on the same list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ l bad",
    rejectContaining "recursion on a larger list cannot prove the empty type" "a recursive call must pass a direct child" $
      compile "let bad: [l: ℕ list, 𝟘] ≔ (0 ‥ l) bad",
    rejectContaining "a partial match proveth nothing" "the match is not exhaustive: missing ‥" $
      compile "let bad: [l: ℕ list, l = empty] ≔ match l { empty ^ reflect }",
    rejectContaining "an empty function needeth an impossible input" "the match is not exhaustive" $
      compile "let bad: [(1 ‥ empty) = (1 ‥ empty), 𝟘] ≔ {}",
    rejectContaining "pointwise same functions are not provably same" "cannot unify" $
      compile "let bad: [f: [ℕ, ℕ], g: [ℕ, ℕ], [n: ℕ, (n f) = (n g)], f = g] ≔ {_ ^ reflect}",
    rejectContaining "a list of one type is not a list of another" "cannot unify ℕ with" $
      compile "let bad: [ℕ list, 𝟚 list] ≔ {l ^ l}",
    rejectContaining "a host binding cannot inhabit an empty type" "requireth a different type" $
      compileAs "soundness_host.tung" "type void: * {}\nlet bad: void ≔ 'add_natural' foreign",
    -- a wrong model proveth `(a e 0) = 0` by induction, and carrying that to a
    -- literal computeth `1 = 0`; only the tested library model is trusted.
    rejectContaining "a program cannot trust its own model of a host operation" "belongeth to type/natural.tung" $
      compileWith
        library
        "soundness_model.tung"
        """
        bring is.tung
        bring type/zero.tung
        let e: [ℕ, ℕ, ℕ] ≔ 'add_natural' foreign { 0, _ ^ 0, _ next, _ ^ 0 }
        let always: [a: ℕ, (a e 0) = 0] ≔ match a { 0 ^ reflect, _ next ^ reflect }
        let claim: [ℕ, *] ≔ {x ^ (x e 0) = 0}
        let move: [n: ℕ, p: n = 1, 1 claim] ≔ p throughbear @ℕ @n @1 @claim (n always)
        let one_zero: [1 = 0, 𝟘] ≔ {}
        let bad: 𝟘 ≔ (1 move reflect) one_zero
        """
  ]
  where
    compile source =
      compileWith library "soundness_test.tung" $
        unlines
          [ "bring is.tung",
            "bring class/algebra/total/hath_multiply.tung",
            "bring type/list.tung",
            "bring type/list_theorem.tung",
            "bring type/natural.tung",
            "bring type/two.tung",
            "bring type/zero.tung"
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
        _ -> Just ("loaded library source differs from " ++ path)

registryCase :: [(FilePath, String)] -> IO Test
registryCase registeredFiles = case lookup "often.tung" [(name, path) | (path, name) <- registeredFiles] of
  Nothing -> pure (pure (Just "the declared library lacks often.tung"))
  Just groundPath -> do
    files <- discover (takeDirectory groundPath)
    let registered = sort (nub (map fst registeredFiles))
        actual = sort (filter ((== ".tung") . takeExtension) files)
    pure . pure $
      if registered == actual
        then Nothing
        else Just ("library registry differs from source tree: " ++ intercalate ", " (registered `symmetricDifference` actual))

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
    checkModule (_, "often.tung") = pure Nothing
    checkModule (path, _) = do
      source <- readFile path
      pure $ case Source.parseSource source of
        Left message -> Just ("parse " ++ path ++ ": " ++ message)
        Right declarations
          | "often.tung" `elem` concatMap importedPaths declarations -> Just (path ++ " imports the ground umbrella")
          | otherwise -> Nothing

groundEffectExportsCase :: Map.Map String String -> Test
groundEffectExportsCase imports =
  pure $ case Harness.checkSource False source imports of
    "type ok" -> Nothing
    actual -> Just ("ground effect exports: " ++ actual)
  where
    source =
      "bring often.tung "
        ++ "let echo:𝟙 effect ≔ read bind { _ ^ >{then, 'a' write_line, random, 0 sleep, only pure} } "
        ++ "let task:(ℤ task) effect ≔ (+1 pure) fork"

systemExplicitCase :: Map.Map String String -> Test
systemExplicitCase imports =
  pure $ case Harness.checkSource False "bring often.tung let args ≔ arguments" imports of
    actual | "type error:" `isPrefixOf` actual -> Nothing
    actual -> Just ("ground unexpectedly exports system effects: " ++ actual)

runnerEffectsCase :: Map.Map String String -> Test
runnerEffectsCase imports =
  pure $ case Harness.checkSource True source imports of
    "type ok" -> Nothing
    actual -> Just ("runner effects: " ++ actual)
  where
    source =
      "bring often.tung bring effect/clock.tung bring effect/process.tung bring effect/system.tung bring web/server.tung bring type/list.tung bring type/optional.tung "
        ++ "let route:[_: _request, _response effect] ≔ 'ok' ok $ pure "
        ++ "let main:𝟙 effect ≔ >{then, arguments, 'TUNG_SETTING' environment, unix_time, 'true' process~run empty, 8080 serve route $ void}"

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
              then Just "host catalogue and foreign declarations differ"
              else
                -- the evaluator performeth an argumentless binding as an effect.
                if any (argumentless . hostSignature) hostBindings
                  then Just "host catalogue inholdeth an argumentless binding that is not an effect"
                  else Nothing
  where
    argumentless HostSignature {hostArguments, hostResult} = null hostArguments && not (isEffect hostResult)
    isEffect (HostApp "effect" _) = True
    isEffect _ = False
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
      | otherwise = Just (path ++ " defineth a class outside the class directory")
    classPrefix = "class/"
    -- module paths keep the documented ascii spellings of symbolic terms.
    asciiName = concatMap (\character -> maybe [character] id (lookup character spellings))
    spellings = [('+', "add"), ('-', "subtract"), ('÷', "divide"), ('%', "divide_leftover"), ('·', "multiply"), ('≤', "at_most"), ('≍', "equal"), ('=', "is"), ('∋', "inhold"), ('‖', "length")]

classNames :: Source.Declaration -> [String]
classNames (Source.ClassDeclaration name _ _) = [name]
classNames (Source.ShownDeclaration declaration) = classNames declaration
classNames _ = []
