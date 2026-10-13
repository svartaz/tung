-- shared assertions preserve the boundary between static evaluator rejection and
-- deliberate runtime failure from an unhandled deed.
module Test.Harness
  ( Group,
    Test,
    group,
    runGroups,
    selectGroups,
    expect,
    expectEq,
    expectPrefix,
    propertyTest,
    parseOk,
    parseErr,
    typeOk,
    typeErr,
    typeErrContaining,
    typeOkWith,
    typeErrWith,
    runnableErr,
    evalOkWith,
    evalTypeErrWith,
    evaluateSource,
    evaluateSourceWithArgs,
    runMainSource,
    checkSource,
    integerSource,
  )
where

import Control.Concurrent (forkIO, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Concurrent.QSem (newQSem, signalQSem, waitQSem)
import Control.Exception (bracket_)
import Control.Monad (foldM, forM, when)
import Data.Functor ((<&>))
import Data.List (elemIndex, intercalate, isInfixOf, isPrefixOf, sortOn)
import Data.Map.Strict qualified as Map
import GHC.Conc (getNumProcessors)
import System.Environment qualified as Environment
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.IO (hFlush, stdout)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (env, proc, readCreateProcessWithExitCode)
import Test.Compile (bookhoardSources, compileProjectDetailed, compileYieldWith, loadBookhoard)
import Test.QuickCheck qualified as QuickCheck
import Test.QuickCheck.Random qualified as QuickCheck
import Text.Read (readMaybe)
import Tung
import Tung.Dependent.Run (ioHost, renderRuntime, requireMain, runMain, runYield)
import Tung.Dependent.Source (CompileFailure (..), FailureKind (..), SourceProgram, parseProgram, snapshotImportPaths, sourceSnapshot)

type Test = IO (Maybe String)

data Group = Group String [Test]

group :: String -> [Test] -> IO Group
group name tests = pure (Group name tests)

runGroups :: [(String, IO Group)] -> IO ()
runGroups groups = do
  progress <- (== Just "1") <$> Environment.lookupEnv "TUNG_TEST_PROGRESS"
  selected <- Environment.lookupEnv "TUNG_TEST_GROUP"
  case selected of
    -- each group runneth in its own process, so caches stay per group. groups
    -- run in parallel, slowest first, and print whole when they finish.
    Nothing -> do
      executable <- Environment.getExecutablePath
      environment <- Environment.getEnvironment
      processors <- getNumProcessors
      jobs <- maybe processors (max 1) . (>>= readMaybe) <$> Environment.lookupEnv "TUNG_TEST_JOBS"
      slots <- newQSem jobs
      printing <- newMVar ()
      let names = sortOn (\name -> maybe (length slowGroups) id (elemIndex name slowGroups)) (map fst groups)
          run name = bracket_ (waitQSem slots) (signalQSem slots) do
            let childEnvironment = ("TUNG_TEST_GROUP", name) : filter ((/= "TUNG_TEST_GROUP") . fst) environment
            (status, output, errors) <- readCreateProcessWithExitCode (proc executable []) {env = Just childEnvironment} ""
            withMVar printing \_ -> putStr (output ++ errors) >> hFlush stdout
            pure status
      finished <- forM names \name -> do
        done <- newEmptyMVar
        _ <- forkIO (run name >>= putMVar done)
        pure done
      statuses <- mapM takeMVar finished
      case [failure | failure@(ExitFailure _) <- statuses] of
        failure : _ -> exitWith failure
        [] -> pure ()
    Just names -> case selectGroups groups names of
      Left message -> putStrLn message >> exitFailure
      Right selected -> go progress 0 [] selected
  where
    go _ count failures [] =
      if null failures
        then putStrLn ("ok (" ++ show count ++ " tests)")
        else mapM_ putStrLn (reverse failures) >> exitFailure
    go progress count failures (action : rest) = do
      Group name tests <- action
      when progress (putStrLn ("running " ++ name) >> hFlush stdout)
      found <- foldM (runTest progress name) failures (zip [1 :: Int ..] tests)
      let nextCount = count + length tests
      nextCount `seq` go progress nextCount found rest
    runTest progress name failures (index, test) = do
      when progress (putStrLn (name ++ "/" ++ show index) >> hFlush stdout)
      result <- test
      -- force each outcome before the next test, releasing successful checks.
      pure $! case result of
        Nothing -> failures
        Just failure -> (name ++ "/" ++ failure) : failures

-- groups that take longest start first, so parallel runs finish together.
slowGroups :: [String]
slowGroups = ["type", "evaluate", "bookhoard", "program", "dependent-module", "dependent-recursion", "dependent-source"]

-- an explicit selection must name existing groups; a typo cannot pass zero tests.
selectGroups :: [(String, a)] -> String -> Either String [a]
selectGroups groups selection = case unknown of
  _ : _ -> Left ("unknown test groups: " ++ intercalate ", " unknown)
  []
    | null requested -> Left "no test groups selected"
    | otherwise -> Right [action | (name, action) <- groups, name `elem` requested]
  where
    requested = words selection
    unknown = filter (`notElem` map fst groups) requested

expect :: String -> Bool -> Test
expect name passed = pure $ if passed then Nothing else Just name

expectEq :: (Eq a, Show a) => String -> a -> a -> Test
expectEq name expected actual =
  expectMessage name (expected == actual) ("expected " ++ show expected ++ ", got " ++ show actual)

expectPrefix :: String -> String -> String -> Test
expectPrefix name prefix actual =
  expectMessage name (prefix `isPrefixOf` actual) ("expected prefix " ++ show prefix ++ ", got " ++ show actual)

propertyTest :: (QuickCheck.Testable property) => String -> property -> Test
propertyTest name property = do
  result <-
    QuickCheck.quickCheckWithResult
      QuickCheck.stdArgs
        { QuickCheck.chatty = False,
          QuickCheck.maxSuccess = 50,
          QuickCheck.replay = Just (QuickCheck.mkQCGen 20260820, 0)
        }
      property
  pure case result of
    QuickCheck.Success {} -> Nothing
    _ -> Just (name ++ ": " ++ QuickCheck.output result)

parseOk, parseErr, typeOk, typeErr, runnableErr :: String -> String -> Test
parseOk name = expectEither name True . parseProgram
parseErr name = expectEither name False . parseProgram
typeOk name source = expectEq name "type ok" (checkSource False source Map.empty)
typeErr name source = expectPrefix name "type error:" (checkSource False source Map.empty)

typeErrContaining :: String -> String -> String -> Test
typeErrContaining name expected source =
  let actual = checkSource False source Map.empty
   in expectMessage name ("type error:" `isPrefixOf` actual && expected `isInfixOf` actual) ("expected error containing " ++ show expected ++ ", got " ++ show actual)

runnableErr name source = expectPrefix name "type error:" (checkSource True source Map.empty)

typeOkWith, typeErrWith :: String -> String -> Map.Map String String -> Test
typeOkWith name source imports = expectEq name "type ok" (checkSource False source imports)
typeErrWith name source imports = expectPrefix name "type error:" (checkSource False source imports)

evalOkWith :: String -> String -> Map.Map String String -> String -> Test
evalOkWith name source imports expected = evaluateSource source imports >>= expectEq name expected

evalTypeErrWith :: String -> String -> Map.Map String String -> Test
evalTypeErrWith name source imports = evaluateSource source imports >>= expectPrefix name "eval error: type error:"

-- `type ok`, or the parse or type error. a runnable source must also define
-- `main`. a test's own modules join the compiled library.
checkSource :: Bool -> String -> Map.Map String String -> String
checkSource runnable source imports = case compiled >>= \modules -> either (Left . failureText) Right (compileProjectDetailed modules (SourceModule "main.tung") source (Map.union imports librarySources)) of
  Left message -> message
  Right program
    | runnable, Left message <- requireMain program -> "type error: " ++ message
    | otherwise -> "type ok"
  where
    (librarySources, compiled) = libraryFor source imports
    failureText CompileFailure {failureKind, failureText = text} = (if failureKind == ParseFailure then "parse error: " else "type error: ") ++ text

-- the yielded value, printed, or `eval error:` and the failure.
evaluateSource :: String -> Map.Map String String -> IO String
evaluateSource = evaluateSourceWithArgs []

evaluateSourceWithArgs :: [String] -> String -> Map.Map String String -> IO String
evaluateSourceWithArgs arguments source imports = do
  let (librarySources, compiled) = libraryFor source imports
  case compiled >>= \modules -> compileYieldWith modules (SourceModule "main.tung") source (Map.union imports librarySources) of
    Left message -> pure ("eval error: type error: " ++ message)
    Right (_, Nothing) -> pure "eval error: nothing is yielded"
    Right (program, Just inferred) -> do
      host <- ioHost arguments
      runYield host program inferred <&> either ("eval error: " ++) (("eval ok: " ++) . renderRuntime)

-- `main` performed: `ok` and its exit status, or the failure.
runMainSource :: String -> Map.Map String String -> IO String
runMainSource source imports = do
  let (librarySources, compiled) = libraryFor source imports
  case compiled >>= \modules -> compileYieldWith modules (SourceModule "main.tung") source (Map.union imports librarySources) of
    Left message -> pure ("type error: " ++ message)
    Right (program, _) -> do
      host <- ioHost []
      case runMain host program of
        Left message -> pure ("type error: " ++ message)
        Right action -> action <&> either ("runtime error: " ++) (\status -> "ok " ++ show status)

-- fixture overrides invalidate all checked interfaces; unchanged tests load
-- only their direct bookhoard imports, whose transitive imports are shared.
libraryFor :: String -> Map.Map String String -> (Map.Map String String, Either String (Map.Map String SourceProgram))
libraryFor source imports = (bookhoardSources, compiled)
  where
    changed = any (\(path, text) -> maybe False (/= text) (Map.lookup path bookhoardSources)) (Map.toList imports)
    paths = filter (`Map.member` bookhoardSources) (snapshotImportPaths (sourceSnapshot source))
    compiled
      | changed = Right Map.empty
      | otherwise = unsafePerformIO do
          cached <- loadBookhoard paths
          -- the root compiler owneth diagnostic order, including parse failures.
          pure (either (const (Right Map.empty)) Right cached)
{-# NOINLINE libraryFor #-}

expectEither :: String -> Bool -> Either String a -> Test
expectEither name wantRight result =
  expectMessage name (wantRight == either (const False) (const True) result) $ case result of
    Left message -> "unexpected rejection: " ++ message
    Right _ -> "unexpected acceptance"

expectMessage :: String -> Bool -> String -> Test
expectMessage name passed detail = pure $ if passed then Nothing else Just (name ++ ": " ++ detail)

-- an integer literal always hath a sign; unsigned digits are a natural.
integerSource :: (Integral a, Show a) => a -> String
integerSource value = (if value < 0 then "" else "+") ++ show value
