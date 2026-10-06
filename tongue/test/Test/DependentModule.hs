-- dependent modules: `use`, `show`, qualification, ambiguity, and cycles.
module Test.DependentModule (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject, compileProjectDetailed, compileProjectWith)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung (SourceSpan (..))
import Tung.Dependent
import Tung.Dependent.Source (CompileFailure (..), FailureKind (..), SourceProgram, parseSource)

group :: IO Harness.Group
group = do
  files <- traverse (\name -> (name,) <$> exampleSource ("dependent_modules/" ++ name)) ["host.tung", "natural.tung", "main.tung"]
  library <- loadLibrary ["_foreign.tung", "ilk/one.tung"]
  Harness.group "dependent-module" (exampleRun library files : replacedFixture library : tests ++ cachedTests)

-- the example's main useþ bare and qualified imports, imported recursion, and
-- bookhoard modules.
exampleRun :: Library -> [(String, String)] -> Test
exampleRun library files = expectEq "a multi-module program runneþ" (Right (Right 0, "tung tung tung tung \n")) do
  main <- maybe (Left "missing main.tung") Right (lookup "main.tung" files)
  program <- compileWith (withModules files library) "main.tung" main
  runSimulated program []

replacedFixture :: Library -> Test
replacedFixture library =
  rejectContaining "a replaced fixture cannot retain a cached constructor" "unknown name 'only'" $
    compileWith
      (withModules [("ilk/one.tung", "show ilk 𝟙:* {}\n")] library)
      "replaced_fixture.tung"
      """
      use ilk/one.tung
      let value:𝟙 ≔ only

      """

tests :: [Test]
tests =
  [ expectEq "shown names are visible bare and qualified" (Right True) $
      checked "use bool.tung\nlet a:bool ≔ yes\nlet b:bool~bool ≔ bool~no\n" [bool],
    expectEq "an alias replaceþ the default namespace" (Right True) $
      checked "use bool.tung truth\nlet a:truth~bool ≔ truth~yes\n" [bool],
    rejectContaining "the default namespace is gone after an alias" "unknown name 'bool~yes'" $
      compile "use bool.tung truth\nlet a ≔ bool~yes\n" [bool],
    rejectContaining "unshown names stay private" "unknown name 'secret'" $
      compile "use bool.tung\nlet a ≔ secret\n" [bool],
    rejectContaining "a bare name shown by two modules is ambiguous" "ambiguous name 'yes'" $
      compile "use bool.tung\nuse other.tung\nlet a ≔ yes\n" [bool, other],
    rejectContaining "re-export ambiguity nameþ visible aliases" "right~yes and left~yes" $
      compile "use first.tung left\nuse second.tung right\nlet a ≔ yes" [bool, other, ("first.tung", "use bool.tung show bool~yes"), ("second.tung", "use other.tung show other~yes")],
    expectEq "qualification resolveþ an ambiguous name" (Right True) $
      checked "use bool.tung\nuse other.tung\nlet a:bool~bool ≔ bool~yes\n" [bool, other],
    expectEq "a local definition shadoweþ a bare import" (Right True) $
      checked "use bool.tung\nilk mine:* { yes: mine }\nlet a:mine ≔ yes\n" [bool],
    rejectContaining "local names still cannot repeat" "top-level name repeateþ" $
      compile "let a ≔ *\nlet a ≔ *\n" [],
    expectEq "one module imported twice keepeþ one identity" (Right True) $
      checked "use bool.tung\nuse wrap.tung\nlet a:bool ≔ yes keep\n" [bool, ("wrap.tung", "use bool.tung\nshow let keep:[bool, bool] ≔ {x ^ x}\n")],
    expectEq "later lambda annotations seeþ earlier binders" (Right True) do
      program <- compile "let shadow ≔ identity\nlet identity ≔ {shadow:*, x:shadow ^ x}" []
      sameNormalIn program "* shadow *" "*",
    expectEq "a later local let doth not hide an earlier global use" (Right True) do
      program <- compile "let before ≔ (let x ≔ later let later ≔ +0 yield x)\nlet later ≔ +1" []
      sameNormalIn program "before" "+1",
    rejectContaining "a use cycle is rejected" "use cycle: a.tung -> b.tung -> a.tung" $
      compile "use a.tung\n" [("a.tung", "use b.tung\n"), ("b.tung", "use a.tung\n")],
    rejectContaining "a missing module is reported" "missing use" $
      compile "use absent.tung\n" [],
    rejectContaining "errors name the module" "in use 'broken.tung'" $
      compile "use broken.tung\n" [("broken.tung", "let bad ≔ unknown\n")],
    rejectContaining "show precedeþ a declaration" "show must precede" $
      parseSource "show use bool.tung\n",
    rejectContaining "use is top-level" "use and show must be top-level" $
      parseSource "let a ≔ (use bool.tung yield *)\n"
  ]
  where
    bool = ("bool.tung", "show ilk bool:* { no: bool, yes: bool }\nlet secret ≔ *\n")
    other = ("other.tung", "show ilk answer:* { yes: answer }\n")

cachedTests :: [Test]
cachedTests =
  [ expectEq "conflicting cached dependencies cannot prove an empty type" (Right expected) do
      cached <- cache "show ilk tag:* {}" "show ilk empty:* {} show let explode:[tag,empty] ≔ {}"
      case compileProjectDetailed cached RootModule "use a.tung\nuse b.tung\nlet impossible:b~empty ≔ a~value b~explode" Map.empty of
        Left failure -> Right failure
        Right _ -> Left "accepted conflicting cached dependencies",
    expectEq "an identical cached diamond keepeþ its checked identities" (Right True) do
      cached <- cache inhabited "show let keep:[tag,tag] ≔ {x ^ x}"
      program <- compileProjectWith cached RootModule "use a.tung\nuse b.tung\nlet answer ≔ a~value b~keep" Map.empty
      sameNormalIn program "answer" "a~value"
  ]
  where
    expected = CompileFailure CheckFailure Nothing (Just (SourceSpan 15 16)) "conflicting definition of 'tag' in use 'b.tung'"
    inhabited = "show ilk tag:* { only:tag }"
    cache dependency source = do
      left <- compileProject (SourceModule "a.tung") "use dep.tung show let value:tag ≔ only" (Map.singleton "dep.tung" inhabited)
      right <- compileProject (SourceModule "b.tung") ("use dep.tung " ++ source) (Map.singleton "dep.tung" dependency)
      pure (Map.fromList [("a.tung", left), ("b.tung", right)])

compile :: String -> [(String, String)] -> Either String SourceProgram
compile source modules = compileProject (SourceModule "root.tung") source (Map.fromList modules)

checked :: String -> [(String, String)] -> Either String Bool
checked source modules = True <$ compile source modules
