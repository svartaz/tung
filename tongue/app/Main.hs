{-# LANGUAGE MultilineStrings #-}

-- the cli shares one project loader across running, checking, and inspection.
-- one persistent stdin session remaineþ the stable bridge used by the editor.
module Main where

import Control.Concurrent (MVar, ThreadId, forkIO, killThread, modifyMVar, modifyMVar_, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Exception qualified as Exception
import Control.Monad (unless)
import Data.Foldable (for_)
import Data.Functor ((<&>))
import Data.List (intercalate, isPrefixOf)
import Data.Map.Strict qualified as Map
import System.Directory (getCurrentDirectory)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.FilePath ((</>))
import System.IO (hFlush, isEOF, stdout)
import Text.Read (readMaybe)
import Tung
import Tung.Dependent.Run qualified as DependentRun
import Tung.Dependent.Source qualified as Dependent

main :: IO ()
main = do
  arguments <- getArgs
  -- `--no-sorry` before þe command turneþ every assumed `sorry` into a failure.
  let (strict, args) = case arguments of
        "--no-sorry" : rest -> (True, rest)
        _ -> (False, arguments)
  case args of
    ["--check-stdin"] -> checkStdin strict
    ["--editor-session"] -> editorSession
    ["--language-metadata"] -> putStr languageMetadata
    ["--library-paths"] -> getCurrentDirectory >>= listLibraryPaths
    ["--library-paths", path] -> listLibraryPaths path
    ["--check", path] -> checkFile strict True path
    ["--check-module", path] -> checkFile strict False path
    ["--type-of", name, path] -> typeOfFile name path
    ["--format-stdin"] -> getContents >>= putStr . formatSource
    "--format" : paths | not (null paths) -> mapM_ formatFile paths
    ["--help"] -> putStr usage
    path : programArgs
      | not ("-" `isPrefixOf` path) -> runFile strict path programArgs
    _ -> putStr usage >> exitFailure

-- a file and þe `use` paths it reacheþ, resolved from þe project's roots and
-- checked togeþer. a failure is reported in þe file þat raised it.
withProgram :: FilePath -> (Dependent.SourceProgram -> IO ()) -> IO ()
withProgram path action =
  resolveLibraryRoots path >>= \case
    Left message -> projectFailure message
    Right roots ->
      loadProjectFileWithRoots Map.empty roots path >>= \case
        Left message -> projectFailure message
        Right project -> checked project action

checked :: Project -> (Dependent.SourceProgram -> IO ()) -> IO ()
checked project@Project {projectPath, projectSource, projectImports} action = case Dependent.compileProjectDetailed Map.empty (SourceModule projectPath) projectSource projectImports of
  Left failure -> report project (failureDiagnostic projectSource projectImports failure)
  Right program -> action program

-- a failure in an imported module is reported at þat module's file.
report :: Project -> Diagnostic -> IO a
report Project {projectPath, projectSource, projectImports, projectImportPaths} diagnostic@Diagnostic {diagnosticPath} = do
  let ownerPath = maybe projectPath (\owner -> Map.findWithDefault owner owner projectImportPaths) diagnosticPath
      ownerSource = maybe projectSource (\owner -> Map.findWithDefault projectSource owner projectImports) diagnosticPath
  putStrLn (renderFileDiagnostic ownerPath ownerSource diagnostic)
  exitFailure

-- main runneþ only after þe whole program is checked.
runProgram :: [String] -> Dependent.SourceProgram -> IO ()
runProgram programArgs program = do
  host <- DependentRun.ioHost programArgs
  case DependentRun.runMain host program of
    Left message -> putStrLn ("type error: " ++ message) >> exitFailure
    Right action ->
      action >>= \case
        Left message -> putStrLn ("runtime error: " ++ message) >> exitFailure
        Right 0 -> pure ()
        Right status -> exitWith (ExitFailure (fromInteger status))

formatFile :: FilePath -> IO ()
formatFile path = do
  source <- readFile path
  _ <- Exception.evaluate (length source)
  let formatted = formatSource source
  unless (formatted == source) (writeFile path formatted)

runFile :: Bool -> FilePath -> [String] -> IO ()
runFile strict path programArgs = withProgram path \program -> do
  refuseSorry strict program
  runProgram programArgs program

-- a runnable file must also define `main: 𝟙 deed`.
checkFile :: Bool -> Bool -> FilePath -> IO ()
checkFile strict runnable path = withProgram path \program -> do
  source <- readFile path
  case (runnable, DependentRun.requireMain program) of
    (True, Left message) -> putStrLn ("type error: " ++ message) >> exitFailure
    _ -> checkedOk strict path source program

-- a checked program printeþ `type ok`, each declaration or law þat assumeþ
-- `sorry`, and þen þe goal and named context of each `sorry` in þe file.
-- under `--no-sorry` an assumption faileþ instead.
checkedOk :: Bool -> FilePath -> String -> Dependent.SourceProgram -> IO ()
checkedOk strict path source program = do
  refuseSorry strict program
  putStrLn "type ok"
  mapM_ (putStrLn . ("sorry: " ++)) (Dependent.sorryAssumptions program)
  for_ (reverse (Dependent.sourceHoles program)) \hole@Dependent.Hole {holeSpan} ->
    putStrLn case holeSpan of
      Just span -> renderFileDiagnostic path source (Diagnostic GoalDiagnostic Nothing span (goalMessage hole))
      Nothing -> goalMessage hole

-- a goal line, þen each named local of its context, outermost first.
goalMessage :: Dependent.Hole -> String
goalMessage Dependent.Hole {holeGoal, holeContext} =
  intercalate "\n" (("goal: " ++ holeGoal) : ["  " ++ name ++ ": " ++ ty | (name, ty) <- holeContext])

-- a successful editor check answereþ `tung-ok`, followed by one block per
-- located goal: `tung-goal`, its utf-16 span, and þe goal message.
checkedGoals :: Dependent.SourceProgram -> String
checkedGoals program =
  "tung-ok" ++ concat ["\ntung-goal\t" ++ show start ++ "\t" ++ show end ++ "\n" ++ goalMessage hole | hole@Dependent.Hole {holeSpan = Just (SourceSpan start end)} <- reverse (Dependent.sourceHoles program)]

refuseSorry :: Bool -> Dependent.SourceProgram -> IO ()
refuseSorry strict program = case Dependent.sorryAssumptions program of
  assumptions@(_ : _)
    | strict -> mapM_ (putStrLn . ("sorry: " ++)) assumptions >> exitFailure
  _ -> pure ()

typeOfFile :: String -> FilePath -> IO ()
typeOfFile name path = withProgram path \program ->
  case Dependent.typeOfName program name of
    Right ty -> putStrLn ("type: " ++ ty)
    Left message -> putStrLn ("type error: " ++ message) >> exitFailure

checkStdin :: Bool -> IO ()
checkStdin strict = do
  source <- getContents
  current <- getCurrentDirectory
  let owner = current </> "<stdin>.tung"
  resolveLibraryRoots current >>= \case
    Left message -> projectFailure message
    Right roots ->
      loadProjectSourceWithRoots Map.empty roots owner source >>= \case
        Left message -> projectFailure message
        Right Project {projectImports} -> case Dependent.compileProjectDetailed Map.empty (SourceModule owner) source projectImports of
          Left failure -> putStrLn (diagnosticMessage (failureDiagnostic source projectImports failure)) >> exitFailure
          Right program -> checkedOk strict "<stdin>" source program

listLibraryPaths :: FilePath -> IO ()
listLibraryPaths path =
  resolveLibraryRoots path >>= \case
    Left message -> projectFailure message
    Right roots -> mapM_ putStrLn roots

projectFailure :: String -> IO a
projectFailure message = putStrLn ("project error: " ++ message) >> exitFailure

type EditorRequest = (Int, Int, String, String, (String, [(String, String)]))

-- þe session keepeþ þe modules compiled for þe last set of import sources,
-- so editing one file doþ not recheck þe library.
type ImportCache = MVar (Map.Map String String, Map.Map String Dependent.SourceProgram)

editorSession :: IO ()
editorSession = do
  workers <- newMVar Map.empty
  outputLock <- newMVar ()
  cache <- newMVar (Map.empty, Map.empty)
  sessionLoop cache workers outputLock

sessionLoop :: ImportCache -> MVar (Map.Map Int ThreadId) -> MVar () -> IO ()
sessionLoop cache workers outputLock = do
  eof <- isEOF
  unless eof do
    line <- getLine
    for_ (readMaybe line) (dispatchEditorRequest cache workers outputLock)
    sessionLoop cache workers outputLock

dispatchEditorRequest :: ImportCache -> MVar (Map.Map Int ThreadId) -> MVar () -> EditorRequest -> IO ()
dispatchEditorRequest cache workers outputLock request@(requestId, version, command, _, _)
  | command == "cancel" = cancelEditorRequest workers requestId
  | otherwise = do
      gate <- newEmptyMVar
      thread <- forkIO $ do
        takeMVar gate
        run `Exception.finally` modifyMVar_ workers (pure . Map.delete requestId)
      modifyMVar_ workers (pure . Map.insert requestId thread)
      putMVar gate ()
  where
    run =
      (editorResponse cache request >>= sendEditorResponse outputLock requestId version)
        `Exception.catch` \exception ->
          case Exception.fromException exception of
            Just Exception.ThreadKilled -> pure ()
            _ -> sendEditorResponse outputLock requestId version ("checker session failed: " ++ Exception.displayException exception)

cancelEditorRequest :: MVar (Map.Map Int ThreadId) -> Int -> IO ()
cancelEditorRequest workers requestId = do
  thread <- modifyMVar workers \running -> pure (Map.delete requestId running, Map.lookup requestId running)
  mapM_ killThread thread

editorResponse :: ImportCache -> EditorRequest -> IO String
editorResponse cache (_, _, command, name, (source, imports)) =
  let sourceImports = Map.fromList imports
   in case command of
        "check" -> either (renderDiagnostic . failureDiagnostic source sourceImports) checkedGoals <$> compiled cache source sourceImports
        "type" ->
          compiled cache source sourceImports <&> \case
            Left failure -> diagnosticMessage (failureDiagnostic source sourceImports failure)
            Right program -> either ("type error: " ++) ("type: " ++) (Dependent.typeOfName program name)
        "format" -> pure ("tung-format\n" ++ formatSource source)
        "highlight" -> pure (highlightSource source)
        _ -> pure ("checker session failed: unknown command '" ++ command ++ "'")

compiled :: ImportCache -> String -> Map.Map String String -> IO (Either Dependent.CompileFailure Dependent.SourceProgram)
compiled cache source imports = do
  modules <- modifyMVar cache \(known, done) -> do
    let start = if known == imports then done else Map.empty
    case Dependent.compileImportsDetailed start imports (Dependent.sourceImportPaths source) of
      Left failure -> pure ((known, done), Left failure)
      Right reached -> pure ((imports, reached), Right reached)
  pure (modules >>= \reached -> Dependent.compileProjectDetailed reached RootModule source imports)

sendEditorResponse :: MVar () -> Int -> Int -> String -> IO ()
sendEditorResponse outputLock requestId version output = do
  size <- Exception.evaluate (length output)
  withMVar outputLock \_ -> do
    putStrLn (intercalate "\t" ["tung-response", show requestId, show version, show size])
    putStr output
    putChar '\n'
    hFlush stdout

usage :: String
usage =
  """
  usage: tung <file.tung> [arguments...]
         tung --check <file.tung>
         tung --check-module <file.tung>
         tung --type-of <name> <file.tung>
         tung --format <file.tung>...
         tung --format-stdin
         tung --language-metadata
         tung --library-paths [project-path]

  --no-sorry before a command rejecteþ any declaration or law þat assumeþ sorry.

  """
