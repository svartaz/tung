{-# LANGUAGE MultilineStrings #-}
{-# LANGUAGE OverloadedStrings #-}

-- the cli shares one project loader across running, checking, and inspection.
-- one persistent stdin session remaineth the stable bridge used by the editor.
module Main where

import Control.Concurrent (MVar, ThreadId, forkIO, killThread, modifyMVar, modifyMVar_, newEmptyMVar, newMVar, putMVar, takeMVar, withMVar)
import Control.Exception qualified as Exception
import Control.Monad (unless)
import Data.Aeson (FromJSON (..), Value, eitherDecodeStrict', encode, object, withObject, (.!=), (.:), (.:?), (.=))
import Data.ByteString.Char8 qualified as ByteString
import Data.ByteString.Lazy qualified as LazyByteString
import Data.Foldable (for_)
import Data.Functor ((<&>))
import Data.List (intercalate, isPrefixOf)
import Data.Map.Strict qualified as Map
import System.Directory (getCurrentDirectory)
import System.Environment (getArgs)
import System.Exit (ExitCode (..), exitFailure, exitWith)
import System.FilePath ((</>))
import System.IO (hFlush, isEOF, stdout)
import Tung
import Tung.Dependent.Run qualified as DependentRun
import Tung.Dependent.Source qualified as Dependent

main :: IO ()
main = do
  arguments <- getArgs
  -- `--no-sorry` before the command turneth every assumed `sorry` into a failure.
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

-- a project loaded from the library roots of `base`, and the `use` paths it
-- reacheth, checked together.
withProject :: FilePath -> ([FilePath] -> IO (Either String Project)) -> (Project -> Diagnostic -> IO ()) -> (Dependent.SourceProgram -> IO ()) -> IO ()
withProject base load failed action =
  resolveLibraryRoots base >>= \case
    Left message -> projectFailure message
    Right roots ->
      load roots >>= \case
        Left message -> projectFailure message
        Right project@Project {projectPath, projectSource, projectImports, projectSnapshot, projectImportSnapshots} ->
          case fst <$> Dependent.compileSnapshot Map.empty (SourceModule projectPath) projectSnapshot projectImportSnapshots of
            Left failure -> failed project (failureDiagnostic projectSource projectImports failure)
            Right program -> action program

-- a file's failure is reported in the file that raised it.
withProgram :: FilePath -> (Dependent.SourceProgram -> IO ()) -> IO ()
withProgram path = withProject path (`loadProjectFile` path) report

-- a failure in an imported module is reported at that module's file.
report :: Project -> Diagnostic -> IO a
report Project {projectPath, projectSource, projectImports, projectImportPaths} diagnostic@Diagnostic {diagnosticPath} = do
  let ownerPath = maybe projectPath (\owner -> Map.findWithDefault owner owner projectImportPaths) diagnosticPath
      ownerSource = maybe projectSource (\owner -> Map.findWithDefault projectSource owner projectImports) diagnosticPath
  putStrLn (renderFileDiagnostic ownerPath ownerSource diagnostic)
  exitFailure

-- main runneth only after the whole program is checked.
runProgram :: [String] -> Dependent.SourceProgram -> IO ()
runProgram programArgs program = do
  host <- DependentRun.ioHost programArgs
  case DependentRun.runMain host program of
    Left message -> typeFailure message
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
    (True, Left message) -> typeFailure message
    _ -> checkedOk strict path source program

-- a checked program printeth `type ok`, each declaration or law that assumeth
-- `sorry`, and then the goal and named context of each `sorry` in the file.
-- under `--no-sorry` an assumption faileth instead.
checkedOk :: Bool -> FilePath -> String -> Dependent.SourceProgram -> IO ()
checkedOk strict path source program = do
  refuseSorry strict program
  putStrLn "type ok"
  mapM_ (putStrLn . ("sorry: " ++)) (Dependent.sorryAssumptions program)
  mapM_ (putStrLn . ("orsetting: " ++)) (Dependent.orsendAssumptions program)
  for_ (reverse (Dependent.sourceHoles program)) \hole@Dependent.Hole {holeSpan} ->
    putStrLn case holeSpan of
      Just span -> renderFileDiagnostic path source (Diagnostic GoalDiagnostic Nothing span (goalMessage hole))
      Nothing -> goalMessage hole

-- a goal line, then each named local of its context, outermost first.
goalMessage :: Dependent.Hole -> String
goalMessage Dependent.Hole {holeGoal, holeContext} =
  intercalate "\n" (("goal: " ++ holeGoal) : ["  " ++ name ++ ": " ++ ty | (name, ty) <- holeContext])

-- goals use the same structured locations as errors; messages remain prose.
checkedGoals :: Dependent.SourceProgram -> [Diagnostic]
checkedGoals program =
  [Diagnostic GoalDiagnostic Nothing span (goalMessage hole) | hole@Dependent.Hole {holeSpan = Just span} <- reverse (Dependent.sourceHoles program)]

refuseSorry :: Bool -> Dependent.SourceProgram -> IO ()
refuseSorry strict program = case Dependent.sorryAssumptions program of
  assumptions@(_ : _)
    | strict -> mapM_ (putStrLn . ("sorry: " ++)) assumptions >> exitFailure
  _ -> pure ()

typeOfFile :: String -> FilePath -> IO ()
typeOfFile name path = withProgram path \program ->
  case Dependent.typeOfName program name of
    Right ty -> putStrLn ("type: " ++ ty)
    Left message -> typeFailure message

-- standard input is checked as a file in the current directory. it hath no
-- file position, so a failure printeth only its message.
checkStdin :: Bool -> IO ()
checkStdin strict = do
  source <- getContents
  current <- getCurrentDirectory
  withProject current (\roots -> loadProjectSource roots (current </> "<stdin>.tung") source) (\_ diagnostic -> putStrLn (diagnosticMessage diagnostic) >> exitFailure) (checkedOk strict "<stdin>" source)

listLibraryPaths :: FilePath -> IO ()
listLibraryPaths path =
  resolveLibraryRoots path >>= \case
    Left message -> projectFailure message
    Right roots -> mapM_ putStrLn roots

typeFailure :: String -> IO a
typeFailure message = putStrLn ("type error: " ++ message) >> exitFailure

projectFailure :: String -> IO a
projectFailure message = putStrLn ("project error: " ++ message) >> exitFailure

-- each utf-8 line is one json value. the protocol version is independent of
-- the document version, which identifyeth the source snapshot being checked.
data EditorRequest = EditorRequest
  { requestId :: Int,
    requestVersion :: Int,
    requestCommand :: String,
    requestName :: String,
    requestSource :: String,
    requestImports :: Map.Map String String
  }

instance FromJSON EditorRequest where
  parseJSON = withObject "editor request" \request -> do
    protocol <- request .: "protocol"
    unless (protocol == (1 :: Int)) (fail "unsupported editor protocol")
    EditorRequest
      <$> request .: "id"
      <*> request .: "version"
      <*> request .: "command"
      <*> request .:? "name" .!= ""
      <*> request .: "source"
      <*> request .: "imports"

-- the session keepeth the modules compiled for the last set of import sources,
-- so editing one file doth not recheck the library.
type ImportCache = MVar (Map.Map String String, Map.Map String Dependent.SourceProgram, Maybe (String, Either Dependent.CompileFailure Dependent.SourceProgram))

editorSession :: IO ()
editorSession = do
  workers <- newMVar Map.empty
  outputLock <- newMVar ()
  cache <- newMVar (Map.empty, Map.empty, Nothing)
  sessionLoop cache workers outputLock

sessionLoop :: ImportCache -> MVar (Map.Map Int ThreadId) -> MVar () -> IO ()
sessionLoop cache workers outputLock = go 0
  where
    go previousId = do
      eof <- isEOF
      unless eof do
        line <- ByteString.getLine
        request@EditorRequest {requestId, requestCommand} <- either (ioError . userError . ("invalid editor request: " ++)) pure (eitherDecodeStrict' line)
        unless (requestCommand == "cancel" || requestId > previousId) (ioError (userError "editor request ids must increase"))
        dispatchEditorRequest cache workers outputLock request
        go (if requestCommand == "cancel" then previousId else requestId)

dispatchEditorRequest :: ImportCache -> MVar (Map.Map Int ThreadId) -> MVar () -> EditorRequest -> IO ()
dispatchEditorRequest cache workers outputLock request@EditorRequest {..}
  | requestCommand == "cancel" = cancelEditorRequest workers outputLock requestId
  | otherwise = do
      gate <- newEmptyMVar
      thread <- forkIO $ do
        takeMVar gate
        run `Exception.finally` modifyMVar_ workers (pure . Map.delete requestId)
      modifyMVar_ workers (pure . Map.insert requestId thread)
      putMVar gate ()
  where
    run =
      (editorResponse cache request >>= sendEditorResponse outputLock requestId requestVersion)
        `Exception.catch` \exception ->
          case Exception.fromException exception of
            Just Exception.ThreadKilled -> pure ()
            _ -> sendEditorResponse outputLock requestId requestVersion (editorError ("checker session failed: " ++ Exception.displayException exception))

cancelEditorRequest :: MVar (Map.Map Int ThreadId) -> MVar () -> Int -> IO ()
cancelEditorRequest workers outputLock requestId =
  -- cancellation must not interrupt a response halfway through its json line.
  withMVar outputLock \_ -> do
    thread <- modifyMVar workers \running -> pure (Map.delete requestId running, Map.lookup requestId running)
    mapM_ killThread thread

editorResponse :: ImportCache -> EditorRequest -> IO Value
editorResponse cache EditorRequest {requestCommand, requestName, requestSource = source, requestImports = imports} =
  case requestCommand of
    "check" ->
      compiled cache source imports <&> \result ->
        object ["kind" .= ("check" :: String), "diagnostics" .= either (pure . failureDiagnostic source imports) checkedGoals result]
    "type" ->
      compiled cache source imports <&> \case
        Left failure -> editorError (diagnosticMessage (failureDiagnostic source imports failure))
        Right program -> either (editorError . ("type error: " ++)) (\ty -> object ["kind" .= ("type" :: String), "type" .= ty]) (Dependent.typeOfName program requestName)
    "format" -> pure (object ["kind" .= ("format" :: String), "source" .= formatSource source])
    "highlight" -> pure (object ["kind" .= ("highlight" :: String), "roles" .= highlightSource source])
    _ -> pure (editorError ("checker session failed: unknown command '" ++ requestCommand ++ "'"))

editorError :: String -> Value
editorError message = object ["kind" .= ("error" :: String), "message" .= message]

compiled :: ImportCache -> String -> Map.Map String String -> IO (Either Dependent.CompileFailure Dependent.SourceProgram)
compiled cache source imports = modifyMVar cache \previous@(known, done, root) ->
  case root of
    Just (text, result) | known == imports && text == source -> pure (previous, result)
    _ -> do
      let snapshot = Dependent.sourceSnapshot source
          modules = Map.map Dependent.sourceSnapshot imports
          start = if known == imports then done else Map.empty
      case Dependent.compileImports start modules (Dependent.snapshotImportPaths snapshot) of
        Left failure -> pure ((imports, start, Just (source, Left failure)), Left failure)
        Right reached -> do
          let result = fst <$> Dependent.compileSnapshot reached RootModule snapshot modules
          _ <- Exception.evaluate result
          pure ((imports, reached, Just (source, result)), result)

sendEditorResponse :: MVar () -> Int -> Int -> Value -> IO ()
sendEditorResponse outputLock requestId version output = do
  let response = encode (object ["protocol" .= (1 :: Int), "id" .= requestId, "version" .= version, "result" .= output])
  _ <- Exception.evaluate (LazyByteString.length response)
  withMVar outputLock \_ -> do
    LazyByteString.hPut stdout response
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

  --no-sorry before a command rejecteth any declaration or law that assumeth sorry.

  """
