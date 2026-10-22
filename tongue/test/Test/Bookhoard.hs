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
    compile source = compileWith library "is_test.tung" ("bring is.tung\n" ++ source)

-- canonical finite sets prove their laws in identity, with no added assumptions.
setCases :: Library -> [Test]
setCases library =
  [ expectEq "finite set laws have no holes or axioms" (Right ()) do
      program <- compile laws
      audits <- traverse (Source.auditProof program) ["yoke_swap", "meet_swap", "yoke_associate", "distribute", "least", "same_sound"]
      mapM_ (Source.verifyProof program True (Just [])) audits,
    expectEq "finite sets normalise order, repetition, and empty yokes" (Right (replicate 6 True)) do
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
      bring ilk/set.tung
      bring ilk/list.tung
      bring ilk/two.tung
      bring flock/hath_inhold.tung
      bring flock/hath_same.tung
      bring flock/order/order_whole.tung
      bring flock/order/semilattice_lower.tung
      bring flock/order/semilattice_upper.tung
      bring flock/order/semilattice_upper_hemmed.tung
      bring flock/order/lattice_spreadsome.tung
      bring flock/same_to_is.tung
      bring is.tung
      """
    values =
      """
      let left ≔ (yea ‥ (nay ‥ (yea ‥ list~empty))) set~from_list
      let right ≔ (set~empty set~put nay) set~put yea
      """
    laws =
      """
      let yoke_swap:[@α:*, @:α order_whole, a:α set, b:α set, (a ⋎ b) = (b ⋎ a)] ≔ a ⋎_swap b
      let meet_swap:[@α:*, @:α order_whole, a:α set, b:α set, (a ⋏ b) = (b ⋏ a)] ≔ a ⋏_swap b
      let yoke_associate:[@α:*, @:α order_whole, a:α set, b:α set, c:α set, ((a ⋎ b) ⋎ c) = (a ⋎ (b ⋎ c))] ≔ a ⋎_⋎ b c
      let distribute:[@α:*, @:α order_whole, a:α set, b:α set, c:α set, (a ⋏ (b ⋎ c)) = ((a ⋏ b) ⋎ (a ⋏ c))] ≔ a ⋏_⋎ b c
      let least:[@α:*, @:α order_whole, a:α set, (set~empty ⋎ a) = a] ≔ a ⟂_⋎
      let same_sound:[@α:*, @:α order_whole, a:α set, b:α set, (a ≍ b) = yea, a = b] ≔ a ≍_= b
      """

-- each ℕ host operation computeth natively on literals and unfoldeth its
-- structural model otherwise; the two must agree, and proofs may use the model.
numberCases :: Library -> [Test]
numberCases library =
  [ agreement "ℕ" (libraryModule library "ilk/kindful.tung") ["same", "at_most", "eke", "offdraw", "fold", "deal_leftover"] (0, 12) (show :: Int -> String),
    agreement "ℤ" (libraryModule library "ilk/wholetale.tung") ["same", "at_most", "eke", "offdraw", "fold", "deal_leftover"] (-12, 12) signed,
    agreement "unicode" (libraryModule library "ilk/unicode.tung") ["same", "at_most"] (0, 3) (\index -> ['`', staffs !! index]),
    agreement "string" (libraryModule library "ilk/string/building.tung") ["same_string", "at_most_string", "yoke_string"] (0, 40) (\index -> "'" ++ spelled index ++ "'"),
    expectEq "a modelled operation is proved by computation and by induction" (Right ()) $
      () <$ compileWith library "kindful_soothing.tung" proofs
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
    staffs = "zλ😀a"
    spelled 0 = ""
    spelled index = staffs !! ((index - 1) `mod` 4) : spelled ((index - 1) `div` 4)
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
      bring ilk/kindful.tung
      bring flock/algebra/whole/hath_eke.tung
      bring is.tung
      let right_naught: [n: ℕ, (n + 0) = n] ≔ eftbend
      let left_naught: [n: ℕ, (0 + n) = n] ≔
        match n {
          0 ^ eftbend,
          k next ^ {x: ℕ ^ x next} leibnitz (k left_naught)
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
    compile source = compileWith library "yoneda_test.tung" ("bring ilk/maybe.tung\nbring often.tung\nbring yoneda.tung\n" ++ source)
    compileCo source = compileWith library "coyoneda_test.tung" ("bring ilk/maybe.tung\nbring often.tung\nbring yoneda_co.tung\n" ++ source)

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
      () <$ compile "let twice: ((minus /) /) = minus ≔ minus /_/\nlet spun: ((plus · minus) /) = ((minus /) · (plus /)) ≔ plus /_over_· minus",
    expectEq "the homomorphism theorems apply to a concrete homomorphism" (Right ()) $
      () <$ compile "bring group_likeshaper.tung\nlet trivial: [mark, mark] ≔ {_ ^ plus}\nlet hom: trivial likeshaped ≔ {_, _ ^ eftbend}\nlet sent: ((one: mark) trivial) = one ≔ trivial one_f hom\nlet same: (plus trivial) = (minus trivial) ≔ trivial kernel_fibre hom plus minus (trivial fibre_kernel hom plus minus eftbend)",
    rejectContaining "a map that turneth signs is no homomorphism" "cannot unify" $
      compile "bring group_likeshaper.tung\nlet spin: [mark, mark] ≔ {plus ^ minus, minus ^ plus}\nlet bad: spin likeshaped ≔ {_, _ ^ eftbend}",
    rejectContaining "a value without an inverse maketh no group" "cannot unify" $
      compileWith library "group_test.tung" "bring often.tung\nbring is.tung\nbring flock/algebra/whole/group_fold.tung\nbizen: 𝟚 group_· { let /: [a:] ≔ a let ·_/ ≔ {yea ^ eftbend, nay ^ eftbend} let /_· ≔ {yea ^ eftbend, nay ^ eftbend} }"
  ]
  where
    compile source = compileWith library "group_test.tung" (sign ++ source)
    sign =
      """
      bring flock/algebra/whole/group_fold.tung
      bring flock/algebra/whole/hath_fold.tung
      bring flock/algebra/whole/hath_one.tung
      bring flock/algebra/whole/monoid_fold.tung
      bring flock/algebra/whole/semigroup_fold.tung
      bring is.tung
      ilk mark: * { plus: mark, minus: mark }
      bizen: mark hath_· { let · ≔ {plus, b ^ b, minus, plus ^ minus, minus, minus ^ plus} }
      bizen: mark hath_one { let one ≔ plus }
      bizen: mark semigroup_· { let ·_· ≔ {plus, _, _; minus, plus, _; minus, minus, plus; minus, minus, minus ^ eftbend} }
      bizen: mark monoid_· { let one_· ≔ {plus; minus ^ eftbend} let ·_one ≔ {plus; minus ^ eftbend} }
      bizen: mark group_· { let /: [a:] ≔ a let ·_/ ≔ {plus; minus ^ eftbend} let /_· ≔ {plus; minus ^ eftbend} }

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
    compile source = compileWith library "module_test.tung" ("bring often.tung\nbring flock/algebra/whole/module.tung\n" ++ source)

-- a relation with nothing smaller is well-founded, and recursion on it runneth
-- the step once.
-- the discrete topology satisfieth every law, so every fall out of it is
-- steady, also after another; a bizen whose whole deal is not open is rejected.
-- lying under goeth through meets, but a deal lieth not under its meet.
topologyCases :: Library -> [Test]
topologyCases library =
  [ expectEq "the discrete topology maketh every fall steady" (Right ()) $
      () <$ compile discrete,
    rejectContaining "a topology must open the whole deal" "cannot unify one~𝟙 with naught~𝟘" $
      compile
        """
        ilk point: * { lone: point }
        bizen: point topology {
          let open: [_:] ≔ 𝟘
          let whole_open ≔ only
          let empty_open ≔ only
          let meet_open: [_:, _:, _:, _:] ≔ only
          let yoke_open: [_:, _:] ≔ only
        }
        """,
    expectEq "lying under goeth through meets" (Right ()) $
      ()
        <$ compile
          """
          let left_twice: [@α: *, u: [α, *], v: [α, *], w: [α, *], ((u meet v) meet w) underset u]
            ≔ ((u meet v) meet w) underset_throughgo (u meet v) u ((u meet v) meet_underset_former w) (u meet_underset_former v)
          """,
    rejectContaining "a deal lieth not under its meet" "cannot unify" $
      compile "let bad: [@α: *, u: [α, *], v: [α, *], u underset (u meet v)] ≔ {_, held ^ held}"
  ]
  where
    compile source = compileWith library "topology_test.tung" (imports ++ "\n" ++ source)
    imports =
      """
      bring flock/algebra/half/semigroupoid.tung
      bring flock/topology.tung
      bring ilk/naught.tung
      bring ilk/one.tung
      """
    discrete =
      """
      ilk discrete: [α: *, *] { lay: [α, α discrete] }
      bizen: [@α: *, (α discrete) topology] {
        let open: [_:] ≔ 𝟙
        let whole_open ≔ only
        let empty_open ≔ only
        let meet_open: [_:, _:, _:, _:] ≔ only
        let yoke_open: [_:, _:] ≔ only
      }
      let discrete_steady: [@α: *, @β: *, @: β topology, f: [α discrete, β], f steady] ≔ {_, _ ^ only}
      let both: [@α: *, @β: *, @γ: *, @: γ topology, f: [α discrete, β discrete], g: [β discrete, γ], (f ▷ g) steady]
        ≔ f ▷_steady g (f discrete_steady) (g discrete_steady)
      """

-- flock laws must rule out lax bizens: euclidean dealing yieldeth an outcome
-- for every dealer but naught, and a half order is witherevenmete in `=`, so
-- a preorder with a sameness that holdeth everywhere is not one.
lawCases :: Library -> [Test]
lawCases library =
  [ expectEq "dealing by a dealer other than naught yieldeth an outcome" (Right ()) $
      ()
        <$ compileWith
          library
          "euclidean_test.tung"
          """
          bring flock/algebra/whole/euclidean.tung
          bring flock/algebra/whole/hath_deal_leftover.tung
          bring ilk/maybe.tung
          bring ilk/two.tung
          bring ilk/wholetale.tung
          bring is.tung
          let dealt: ((+7 % -2) is_some) = yea ≔ +7 %_some -2 {k ^ match k {}}
          """,
    rejectContaining "a lax sameness maketh no half order" "cannot unify" $
      compileWith
        library
        "half_order_test.tung"
        """
        bring flock/hath_same.tung
        bring flock/order/hath_at_most.tung
        bring flock/order/order_half.tung
        bring ilk/two.tung
        bring is.tung
        ilk rank: * { lesser: rank, greater: rank }
        bizen: rank hath_≍ { let ≍ ≔ {_, _ ^ yea} }
        bizen: rank order_half {
          let ≤ ≔ {_, _ ^ yea}
          let ≤_eftbend ≔ {_ ^ eftbend}
          let ≤_witherevenmete ≔ {_, _ ^ eftbend}
          let ≤_throughgo ≔ {_, _, _ ^ eftbend}
          let ≤_= ≔ {_, _, _, _ ^ eftbend}
        }
        """
  ]

groundedCases :: Library -> [Test]
groundedCases library =
  [ expectEq "well-founded selfcalling computeth its step" (Right True) do
      program <- compileWith library "grounded_test.tung" source
      sameNormalIn program "answer" "4"
  ]
  where
    source =
      """
      bring ilk/grounded.tung
      bring ilk/naught.tung
      let never: [_: ℕ, _: ℕ, *] ≔ 𝟘
      let founded: ℕ wellgrounded never ≔ {x ^ {y, impossible ^ impossible ({}: [𝟘, ℕ grounded never y])} ground}
      let answer: ℕ ≔ founded wellgrounded_selfcall {x, _ ^ x next} 3
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
    rejectContaining "onhanging is not commutative" "cannot unify" $
      compile "let bad: [a: ℕ list, b: ℕ list, (a · b) = (b · a)] ≔ match a { empty ^ (b ·_empty) evenmete, first ‥ leftover ^ (first ‥) leibnitz (leftover bad b) }",
    rejectContaining "distinct lists are not same" "cannot unify 1 with 2" $
      compile "let bad: (1 ‥ empty) = (2 ‥ empty) ≔ eftbend",
    rejectContaining "reversing is not the sameness" "cannot unify" $
      compile "let bad: [l: ℕ list, (l eftwend) = l] ≔ match l { empty ^ eftbend, first ‥ leftover ^ (first ‥) leibnitz (leftover bad) }",
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
    rejectContaining "a host binding cannot inhabit an empty type" "requireth a different ilk" $
      compileAs "soundness_host.tung" "ilk void: * {}\nlet bad: void ≔ 'eke_kindful' fremmed",
    -- a wrong model proveth `(a e 0) = 0` by induction, and carrying that to a
    -- literal computeth `1 = 0`; only the tested bookhoard model is trusted.
    rejectContaining "a program cannot trust its own model of a host operation" "belongeth to ilk/kindful.tung" $
      compileWith
        library
        "soundness_model.tung"
        """
        bring is.tung
        bring ilk/naught.tung
        let e: [ℕ, ℕ, ℕ] ≔ 'eke_kindful' fremmed { 0, _ ^ 0, _ next, _ ^ 0 }
        let always: [a: ℕ, (a e 0) = 0] ≔ match a { 0 ^ eftbend, _ next ^ eftbend }
        let claim: [ℕ, *] ≔ {x ^ (x e 0) = 0}
        let move: [n: ℕ, p: n = 1, 1 claim] ≔ p throughbear @ℕ @n @1 @claim (n always)
        let one_naught: [1 = 0, 𝟘] ≔ {}
        let bad: 𝟘 ≔ (1 move eftbend) one_naught
        """
  ]
  where
    compile source =
      compileWith library "soundness_test.tung" $
        unlines
          [ "bring is.tung",
            "bring flock/algebra/whole/hath_fold.tung",
            "bring ilk/list.tung",
            "bring ilk/list_setting.tung",
            "bring ilk/kindful.tung",
            "bring ilk/two.tung",
            "bring ilk/naught.tung"
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
registryCase registeredFiles = case lookup "often.tung" [(name, path) | (path, name) <- registeredFiles] of
  Nothing -> pure (pure (Just "the declared bookhoard library lacks often.tung"))
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
    checkModule (_, "often.tung") = pure Nothing
    checkModule (path, _) = do
      source <- readFile path
      pure $ case Source.parseSource source of
        Left message -> Just ("parse " ++ path ++ ": " ++ message)
        Right declarations
          | "often.tung" `elem` concatMap importedPaths declarations -> Just (path ++ " imports the ground umbrella")
          | otherwise -> Nothing

groundDeedExportsCase :: Map.Map String String -> Test
groundDeedExportsCase imports =
  pure $ case Harness.checkSource False source imports of
    "ilk ok" -> Nothing
    actual -> Just ("ground deed exports: " ++ actual)
  where
    source =
      "bring often.tung "
        ++ "let echo:𝟙 deed ≔ read bind { _ ^ >{then, 'a' write_line, random, 0 sleep, only sheer} } "
        ++ "let task:(ℤ task) deed ≔ (+1 sheer) fork"

systemExplicitCase :: Map.Map String String -> Test
systemExplicitCase imports =
  pure $ case Harness.checkSource False "bring often.tung let args ≔ arguments" imports of
    actual | "ilk error:" `isPrefixOf` actual -> Nothing
    actual -> Just ("ground unexpectedly exports system deeds: " ++ actual)

runnerDeedsCase :: Map.Map String String -> Test
runnerDeedsCase imports =
  pure $ case Harness.checkSource True source imports of
    "ilk ok" -> Nothing
    actual -> Just ("runner deeds: " ++ actual)
  where
    source =
      "bring often.tung bring deed/clock.tung bring deed/process.tung bring deed/system.tung bring web/server.tung bring ilk/list.tung bring ilk/maybe.tung "
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
