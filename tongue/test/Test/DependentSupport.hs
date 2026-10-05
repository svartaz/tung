-- shared helpers for the dependent core and source test groups.
module Test.DependentSupport
  ( level,
    sort,
    reject,
    rejectContaining,
    eraseLevels,
    compileAs,
    Library,
    loadLibrary,
    withModules,
    compileWith,
    sameNormalIn,
    exampleSource,
    World (..),
    world,
    runWorld,
    runSimulated,
  )
where

import Control.Monad (filterM)
import Control.Monad.Trans.State.Strict (State, gets, modify', runState, state)
import Data.Either (isLeft)
import Data.Functor.Identity (Identity (..))
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath (takeDirectory, (</>))
import Test.Harness (Test, expect)
import Tung (readLibraryImports)
import Tung.Dependent
import Tung.Dependent.Run (HostIO (..), Request, Response, Runtime, runMain)
import Tung.Dependent.Source (SourceProgram, compileModules, compileProjectWith, compileSource, normaliseSourceExpression)

level :: Int -> Level
level n = iterate LSucc LZero !! n

sort :: Int -> Term
sort = Sort . level

reject :: String -> Either String a -> Test
reject label = expect label . isLeft

rejectContaining :: String -> String -> Either String a -> Test
rejectContaining label expected result = expect (label ++ ": " ++ message) (isLeft result && expected `isInfixOf` message)
  where
    message = either id (const "unexpected acceptance") result

-- separate source elaborations may generalise their universe holes differently.
eraseLevels :: Term -> Term
eraseLevels = \case
  Global symbol levels -> Global symbol (LZero <$ levels)
  Sort _ -> Sort LZero
  term -> runIdentity (mapChildren (\_ -> Identity . eraseLevels) term)

compileAs :: FilePath -> String -> Either String SourceProgram
compileAs = compileSource . SourceModule

-- bookhoard sources and þe modules a group useþ, compiled once.
data Library = Library (Map.Map String String) (Map.Map String SourceProgram)

loadLibrary :: [String] -> IO Library
loadLibrary paths = do
  sources <- readLibraryImports "." >>= either fail pure
  compiled <- either fail pure (compileModules sources paths)
  pure (Library sources compiled)

-- furþer sources beside bookhoard, keyed by use path. a changed source
-- invalidateþ every cached module, including its transitive dependants.
withModules :: [(String, String)] -> Library -> Library
withModules modules (Library sources compiled) =
  let added = Map.fromList modules
      changed = any (\(path, source) -> maybe False (/= source) (Map.lookup path sources)) (Map.toList added)
   in Library (Map.union added sources) (if changed then Map.empty else compiled)

-- a source may use any bookhoard module; loaded ones are not checked again.
compileWith :: Library -> FilePath -> String -> Either String SourceProgram
compileWith (Library sources compiled) name source = compileProjectWith compiled (SourceModule name) source sources

-- both expressions are checked, normalised, and compared without universe levels.
sameNormalIn :: SourceProgram -> String -> String -> Either String Bool
sameNormalIn program actual expected = do
  first <- normaliseSourceExpression program actual
  second <- normaliseSourceExpression program expected
  pure (eraseLevels first == eraseLevels second)

-- examples live in tongue/examples; tests may run from the package or repository root.
exampleSource :: FilePath -> IO String
exampleSource name = getCurrentDirectory >>= search
  where
    search directory = do
      let candidates = [directory </> "examples" </> name, directory </> "tongue" </> "examples" </> name]
      found <- filterM doesFileExist candidates
      case found of
        path : _ -> readFile path
        []
          | takeDirectory directory == directory -> fail ("cannot find examples/" ++ name)
          | otherwise -> search (takeDirectory directory)

-- a deterministic world for the dependent runner.
data World = World
  { worldInput :: [String],
    worldOutput :: String,
    worldFiles :: Map.Map FilePath String,
    worldArguments :: [String],
    worldEnvironment :: [(String, String)],
    -- `web_serve` answereþ each queued request, then reporteþ that none remain.
    worldRequests :: [Request],
    worldResponses :: [Response],
    worldTasks :: Map.Map Int (Either String Runtime)
  }

world :: World
world = World [] "" Map.empty [] [] [] [] Map.empty

runWorld :: World -> SourceProgram -> Either String (Either String Integer, World)
runWorld start program = (`runState` start) <$> runMain simulated program

-- a run from queued input lines to its exit status and written text.
runSimulated :: SourceProgram -> [String] -> Either String (Either String Integer, String)
runSimulated program inputs = fmap worldOutput <$> runWorld world {worldInput = inputs} program

-- random is 0.25, the clock is 1700000000, `echo` is the only program, and
-- tasks finish when forked.
simulated :: HostIO (State World)
simulated =
  HostIO
    { hostWrite = \text -> Right <$> modify' \current -> current {worldOutput = worldOutput current ++ text},
      hostRead =
        gets worldInput >>= \case
          line : rest -> modify' (\current -> current {worldInput = rest}) >> pure (Right line)
          [] -> pure (Left "end of input"),
      hostReadFile = \path -> maybe (Left ("no file " ++ path)) Right . Map.lookup path <$> gets worldFiles,
      hostWriteFile = \path text -> Right <$> modify' \current -> current {worldFiles = Map.insert path text (worldFiles current)},
      hostAppendFile = \path text -> Right <$> modify' \current -> current {worldFiles = Map.insertWith (flip (++)) path text (worldFiles current)},
      hostRandom = pure 0.25,
      hostUnixTime = pure 1700000000,
      hostArguments = gets worldArguments,
      hostEnvironment = \name -> lookup name <$> gets worldEnvironment,
      hostRunProcess = \command inputs -> pure case command of
        "echo" -> Right (0, unwords inputs ++ "\n", "")
        _ -> Left ("no program " ++ command),
      hostFork = \action -> do
        result <- action
        state \current -> let handle = Map.size (worldTasks current) in (handle, current {worldTasks = Map.insert handle result (worldTasks current)}),
      hostWait = \handle -> maybe (Left "unknown task") id . Map.lookup handle <$> gets worldTasks,
      hostWaitFor = \handle _ -> Map.lookup handle <$> gets worldTasks,
      hostCancel = \_ -> pure (),
      hostSleep = \_ -> pure (),
      hostServe = \_ respond ->
        let serve =
              gets worldRequests >>= \case
                [] -> pure (Left "no more requests")
                request : rest -> do
                  modify' \current -> current {worldRequests = rest}
                  respond request >>= \case
                    Left stop -> pure (Right stop)
                    Right response -> modify' (\current -> current {worldResponses = worldResponses current ++ [response]}) >> serve
         in serve
    }
