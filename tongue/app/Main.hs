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
  (strict, allowed, args) <- either (\message -> putStrLn message >> exitFailure) pure (commandOptions arguments)
  case args of
    ["--check-proof", name, path] -> checkProofFile allowed name path
    _ | Just _ <- allowed -> putStrLn "axiom options require --check-proof" >> exitFailure
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

-- proof-policy options precede the command. an explicit empty allowlist
-- cannot be combined with named allowances.
commandOptions :: [String] -> Either String (Bool, Maybe [String], [String])
commandOptions = go False Nothing False
  where
    go _ allowed empty ("--no-sorry" : rest) = go True allowed empty rest
    go strict allowed empty ("--allow-axiom" : name : rest)
      | not ("--" `isPrefixOf` name), not empty = go strict (Just (maybe [] id allowed ++ [name])) False rest
    go _ _ _ ["--allow-axiom"] = Left "--allow-axiom requireth a name"
    go strict allowed _ ("--no-axioms" : rest)
      | maybe True null allowed = go strict (Just []) True rest
    go _ _ _ ("--allow-axiom" : _) = Left "--allow-axiom requireth a name and cannot accompany --no-axioms"
    go _ _ _ ("--no-axioms" : _) = Left "--no-axioms cannot accompany --allow-axiom"
    go strict allowed _ args = Right (strict, allowed, args)

-- a project loaded from the library roots of `base`, and the `use` paths it
-- reacheth, checked together.
withProject :: FilePath -> ([FilePath] -> IO (Either String Project)) -> (Project -> Diagnostic -> [Dependent.Hole] -> IO ()) -> (Dependent.SourceProgram -> IO ()) -> IO ()
withProject base load failed action =
  resolveLibraryRoots base >>= \case
    Left message -> projectFailure message
    Right roots ->
      load roots >>= \case
        Left message -> projectFailure message
        Right project@Project {projectPath, projectSource, projectImports, projectSnapshot, projectImportSnapshots} -> do
          -- imports reuse checked interfaces; newly checked ones are saved.
          directory <- cacheDirectory projectPath
          build <- Dependent.compilerBuild
          let keys = Dependent.cacheKeys build projectImportSnapshots
          cached <- Dependent.loadInterfaces directory projectImportSnapshots keys
          case Dependent.compileImports cached projectImportSnapshots (Dependent.snapshotImportPaths projectSnapshot) of
            Left failure -> failed project (failureDiagnostic projectSource projectImports failure) (Dependent.recoverSnapshotHoles cached (SourceModule projectPath) projectSnapshot projectImportSnapshots)
            Right reached -> do
              Dependent.saveInterfaces directory keys (Map.difference reached cached)
              case fst <$> Dependent.compileSnapshot reached (SourceModule projectPath) projectSnapshot projectImportSnapshots of
                Left failure -> failed project (failureDiagnostic projectSource projectImports failure) (Dependent.recoverSnapshotHoles reached (SourceModule projectPath) projectSnapshot projectImportSnapshots)
                Right program -> action program

-- a file's failure is reported in the file that raised it.
withProgram :: FilePath -> (Dependent.SourceProgram -> IO ()) -> IO ()
withProgram path = withProject path (`loadProjectFile` path) (\project diagnostic _ -> report project diagnostic)

-- a failure in an imported module is reported at that module's file.
report :: Project -> Diagnostic -> IO a
report Project {projectPath, projectSource, projectImports, projectImportPaths} diagnostic@Diagnostic {diagnosticPath} = do
  let ownerPath = maybe projectPath (\owner -> Map.findWithDefault owner owner projectImportPaths) diagnosticPath
      ownerSource = maybe projectSource (\owner -> Map.findWithDefault projectSource owner projectImports) diagnosticPath
  putStrLn (renderFileDiagnostic ownerPath ownerSource diagnostic)
  exitFailure

-- checking still faileth, but unrelated unfinished proofs retain their goals.
reportGoals :: Project -> Diagnostic -> [Dependent.Hole] -> IO ()
reportGoals Project {projectPath, projectSource, projectImports, projectImportPaths} diagnostic holes = do
  let path = maybe projectPath (\owner -> Map.findWithDefault owner owner projectImportPaths) (diagnosticPath diagnostic)
      source = maybe projectSource (\owner -> Map.findWithDefault projectSource owner projectImports) (diagnosticPath diagnostic)
  putStrLn (renderFileDiagnostic path source diagnostic)
  printGoals projectPath projectSource holes
  exitFailure

printGoals :: FilePath -> String -> [Dependent.Hole] -> IO ()
printGoals path source = mapM_ \hole@Dependent.Hole {holeSpan} ->
  putStrLn case holeSpan of
    Just span -> renderFileDiagnostic path source (Diagnostic GoalDiagnostic Nothing span (goalMessage hole))
    Nothing -> goalMessage hole

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
checkFile strict runnable path = withProject path (`loadProjectFile` path) reportGoals \program -> do
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
  printGoals path source (reverse (Dependent.sourceHoles program))

-- a goal line, then each named local of its context, outermost first.
goalMessage :: Dependent.Hole -> String
goalMessage Dependent.Hole {holeGoal, holeContext} =
  intercalate "\n" (("goal: " ++ holeGoal) : ["  " ++ name ++ ": " ++ ty | (name, ty) <- holeContext])

-- goals use the same structured locations as errors; messages remain prose.
holeGoals :: [Dependent.Hole] -> [Diagnostic]
holeGoals holes =
  [Diagnostic GoalDiagnostic Nothing span (goalMessage hole) | hole@Dependent.Hole {holeSpan = Just span} <- holes]

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

-- one theorem is audited independently of unfinished, unrelated declarations.
checkProofFile :: Maybe [String] -> String -> FilePath -> IO ()
checkProofFile override name path = withProgram path \program -> do
  policy <- proofPolicy override path
  case proofResult program policy name of
    Left message -> putStrLn ("proof error: " ++ message) >> exitFailure
    Right (audit, verified) -> do
      putStr (proofReport audit verified)
      either (const exitFailure) pure verified

proofPolicy :: Maybe [String] -> FilePath -> IO (Either String (Maybe [String]))
proofPolicy (Just names) _ = pure (Right (Just names))
proofPolicy Nothing path = proofAxiomPolicy path

proofResult :: Dependent.SourceProgram -> Either String (Maybe [String]) -> String -> Either String (Dependent.ProofAudit, Either String ())
proofResult program policy name = do
  audit <- Dependent.auditProof program name
  pure (audit, policy >>= \allowed -> Dependent.verifyProof program allowed audit)

-- the cli and editor share the compiler's complete, deterministic report.
proofReport :: Dependent.ProofAudit -> Either String () -> String
proofReport audit verified =
  unlines $
    ["proof: " ++ auditName, "type: " ++ auditType]
      ++ (if null auditDependencies then ["dependencies: none"] else map dependencyReport auditDependencies)
      ++ [either ("proof error: " ++) (const "proof ok") verified]
  where
    auditName = Dependent.auditName audit
    auditType = Dependent.auditType audit
    auditDependencies = Dependent.auditDependencies audit
    dependencyReport Dependent.ProofDependency {dependencyName, dependencyType, dependencyKind} =
      case dependencyKind of
        Dependent.SorryDependency -> "sorry: " ++ dependencyName ++ ": " ++ dependencyType
        Dependent.AxiomDependency -> "orsetting: " ++ dependencyName ++ ": " ++ dependencyType
        Dependent.HostDependency key -> "host: " ++ dependencyName ++ " [" ++ key ++ "]: " ++ dependencyType

-- standard input is checked as a file in the current directory. it hath no
-- file position, so a failure printeth only its message.
checkStdin :: Bool -> IO ()
checkStdin strict = do
  source <- getContents
  current <- getCurrentDirectory
  withProject current (\roots -> loadProjectSource roots (current </> "<stdin>.tung") source) (\_ diagnostic holes -> putStrLn (diagnosticMessage diagnostic) >> printGoals "<stdin>" source holes >> exitFailure) (checkedOk strict "<stdin>" source)

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
    requestImports :: Map.Map String String,
    requestPath :: Maybe FilePath,
    requestAllowedAxioms :: Maybe [String]
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
      <*> request .:? "path"
      <*> request .:? "allowedAxioms"

-- the session keepeth checked modules by interface key, so editing one file
-- rechecketh only the modules that depend on it. a request that nameth its
-- file also loadeth and saveth interfaces in that project's disk cache. the
-- last root result is kept for a repeated request.
type CompilationReport = (Either Dependent.CompileFailure Dependent.SourceProgram, [Dependent.Hole])

data ImportCache = ImportCache
  { cacheBuild :: String,
    cacheState :: MVar (Map.Map String Dependent.SourceProgram, Maybe ((String, Map.Map String String), CompilationReport))
  }

editorSession :: IO ()
editorSession = do
  workers <- newMVar Map.empty
  outputLock <- newMVar ()
  build <- Dependent.compilerBuild
  state <- newMVar (Map.empty, Nothing)
  sessionLoop (ImportCache build state) workers outputLock

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
editorResponse cache EditorRequest {requestCommand, requestName, requestSource = source, requestImports = imports, requestPath, requestAllowedAxioms} =
  case requestCommand of
    "check" ->
      compilationReport cache requestPath source imports <&> \(result, holes) ->
        object ["kind" .= ("check" :: String), "diagnostics" .= (either (pure . failureDiagnostic source imports) (const []) result ++ holeGoals holes)]
    "type" ->
      compiled cache requestPath source imports <&> \case
        Left failure -> editorError (diagnosticMessage (failureDiagnostic source imports failure))
        Right program -> either (editorError . ("type error: " ++)) (\ty -> object ["kind" .= ("type" :: String), "type" .= ty]) (Dependent.typeOfName program requestName)
    "proof" ->
      compiled cache requestPath source imports >>= \case
        Left failure -> pure (editorError (diagnosticMessage (failureDiagnostic source imports failure)))
        Right program -> do
          path <- maybe getCurrentDirectory pure requestPath
          policy <- proofPolicy requestAllowedAxioms path
          pure $ either (editorError . ("proof error: " ++)) (uncurry proofResponse) (proofResult program policy requestName)
    "format" -> pure (object ["kind" .= ("format" :: String), "source" .= formatSource source])
    "highlight" -> pure (object ["kind" .= ("highlight" :: String), "roles" .= highlightSource source])
    _ -> pure (editorError ("checker session failed: unknown command '" ++ requestCommand ++ "'"))

editorError :: String -> Value
editorError message = object ["kind" .= ("error" :: String), "message" .= message]

proofResponse :: Dependent.ProofAudit -> Either String () -> Value
proofResponse audit verified =
  object
    [ "kind" .= ("proof" :: String),
      "audit" .= object ["name" .= auditName, "type" .= auditType, "dependencies" .= map dependencyJSON auditDependencies],
      "verified" .= either (const False) (const True) verified,
      "message" .= either id (const "proof ok") verified,
      "report" .= proofReport audit verified
    ]
  where
    auditName = Dependent.auditName audit
    auditType = Dependent.auditType audit
    auditDependencies = Dependent.auditDependencies audit
    dependencyJSON Dependent.ProofDependency {dependencySymbol = SymbolId owner name, dependencyName, dependencyType, dependencyKind} =
      object $
        [ "symbol" .= object ["module" .= moduleName owner, "name" .= name],
          "name" .= dependencyName,
          "type" .= dependencyType
        ]
          ++ case dependencyKind of
            Dependent.SorryDependency -> ["kind" .= ("sorry" :: String)]
            Dependent.AxiomDependency -> ["kind" .= ("axiom" :: String)]
            Dependent.HostDependency key -> ["kind" .= ("host" :: String), "host" .= key]
    moduleName RootModule = "<root>"
    moduleName (SourceModule path) = path
    moduleName PrimitiveModule = "<primitive>"

compiled :: ImportCache -> Maybe FilePath -> String -> Map.Map String String -> IO (Either Dependent.CompileFailure Dependent.SourceProgram)
compiled cache path source imports = fst <$> compilationReport cache path source imports

compilationReport :: ImportCache -> Maybe FilePath -> String -> Map.Map String String -> IO CompilationReport
compilationReport ImportCache {cacheBuild, cacheState} path source imports = modifyMVar cacheState \previous@(memory, root) ->
  case root of
    Just (request, result) | request == (source, imports) -> pure (previous, result)
    _ -> do
      let snapshot = Dependent.sourceSnapshot source
          modules = Map.map Dependent.sourceSnapshot imports
          keys = Dependent.cacheKeys cacheBuild modules
          remembered = Map.mapMaybe (`Map.lookup` memory) keys
      directory <- traverse cacheDirectory path
      loaded <- maybe (pure Map.empty) (\dir -> Dependent.loadInterfaces dir modules (Map.difference keys remembered)) directory
      let start = Map.union remembered loaded
          kept reached = Map.fromList [(key, program) | (name, program) <- Map.toList reached, Just key <- [Map.lookup name keys]]
      case Dependent.compileImports start modules (Dependent.snapshotImportPaths snapshot) of
        Left failure ->
          let result = (Left failure, Dependent.recoverSnapshotHoles start RootModule snapshot modules)
           in pure ((kept start, Just ((source, imports), result)), result)
        Right reached -> do
          mapM_ (\dir -> Dependent.saveInterfaces dir keys (Map.difference reached start)) directory
          let result = fst <$> Dependent.compileSnapshot reached RootModule snapshot modules
              report = (result, either (const (Dependent.recoverSnapshotHoles reached RootModule snapshot modules)) (reverse . Dependent.sourceHoles) result)
          _ <- Exception.evaluate result
          pure ((kept reached, Just ((source, imports), report)), report)

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
         tung --check-proof <name> <file.tung>
         tung --format <file.tung>...
         tung --format-stdin
         tung --language-metadata
         tung --library-paths [project-path]

  --no-sorry before a command rejecteth any declaration or law that assumeth sorry.
  --check-proof always rejecteth reachable sorry and reporteth axioms and hosts.
  --allow-axiom <name> may precede --check-proof repeatedly; --no-axioms alloweth none.
  without either option, --check-proof useth the nearest tung.yaml proof policy.

  """
