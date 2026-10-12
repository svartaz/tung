{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

-- | the dependent runner. checked core terms are evaluated with types and
-- universe levels erased; deeds are inert values until 'runMain' executeth them
-- through a replaceable host interface.
module Tung.Dependent.Run
  ( HostIO (..),
    Runtime,
    Web.Request (..),
    Web.Response (..),
    ioHost,
    runMain,
    requireMain,
    runYield,
    renderRuntime,
  )
where

import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Concurrent.MVar (newEmptyMVar, readMVar, tryPutMVar)
import Control.DeepSeq (rnf)
import Control.Exception (IOException, SomeException, displayException, try)
import Control.Monad (foldM, unless, void, (>=>))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT (..), runExceptT, throwE)
import Data.Functor ((<&>))
import Data.IORef (atomicModifyIORef', newIORef, readIORef)
import Data.List (findIndex, intercalate, sortOn)
import Data.Map.Lazy qualified as Lazy
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.IO qualified as TextIO
import Data.Time.Clock.POSIX (getPOSIXTime)
import GHC.Float (castDoubleToWord64)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO (hFlush, isEOF, stdout)
import System.Process (readProcessWithExitCode)
import System.Timeout (timeout)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Host (matchMain)
import Tung.Dependent.Literal (constructedLiteral, coreConstructor, literalConstructor, literalTypeNames, literalValue, renderLiteral, valueLiteral)
import Tung.Dependent.Source (SourceProgram, sourceEnvironment, sourceGlobal)
import Tung.Dependent.Syntax
import Tung.Identity (SymbolId (..))
import Tung.Name (lastQualifiedSegment)
import Tung.Primitive
  ( HostBinding (..),
    HostSignature (HostSignature, hostVariables),
    HostValue (..),
    consConstructorId,
    emptyConstructorId,
    findForeignBinding,
    integerNegativeId,
    integerPositiveId,
    leftConstructorId,
    naturalSuccessorId,
    nayConstructorId,
    noneConstructorId,
    onlyConstructorId,
    processResultConstructorId,
    productConstructorId,
    pureOperation,
    requestConstructorId,
    responseConstructorId,
    rightConstructorId,
    someConstructorId,
    tableConstructorId,
    yeaConstructorId,
  )
import Tung.Primitive qualified as Primitive
import Tung.Web qualified as Web

-- the trusted operations a deed may perform. a failed console operation endeth
-- the run; other failures reach the program's failure continuation. tests
-- supply a simulated host.
data HostIO m = HostIO
  { hostWrite :: String -> m (Either String ()),
    hostRead :: m (Either String String),
    hostReadFile :: FilePath -> m (Either String String),
    hostWriteFile :: FilePath -> String -> m (Either String ()),
    hostAppendFile :: FilePath -> String -> m (Either String ()),
    -- a float in [0, 1).
    hostRandom :: m Double,
    -- whole seconds since the unix epoch.
    hostUnixTime :: m Integer,
    hostArguments :: m [String],
    hostEnvironment :: String -> m (Maybe String),
    -- status, standard output, and standard error.
    hostRunProcess :: String -> [String] -> m (Either String (Integer, String, String)),
    -- a task runneth its action, possibly concurrently, under a fresh handle.
    hostFork :: m (Either String Runtime) -> m Int,
    hostWait :: Int -> m (Either String Runtime),
    -- milliseconds; nothing when the task hath not finished in time.
    hostWaitFor :: Int -> Integer -> m (Maybe (Either String Runtime)),
    hostCancel :: Int -> m (),
    hostSleep :: Integer -> m (),
    -- serve until the transport faileth, as left, or a response stopth it, as right.
    hostServe :: forall stop. Integer -> (Web.Request -> m (Either stop Web.Response)) -> m (Either String stop)
  }

-- the process host. tasks run on threads; a cancelled task faileth.
ioHost :: [String] -> IO (HostIO IO)
ioHost arguments = do
  tasks <- newIORef (0 :: Int, Map.empty)
  let task handle = Map.lookup handle . snd <$> readIORef tasks
  pure
    HostIO
      { hostWrite = \text -> Right <$> (putStr text >> hFlush stdout),
        hostRead = do
          hFlush stdout
          ended <- isEOF
          if ended then pure (Left "end of input") else Right <$> getLine,
        hostReadFile = \path -> io (Text.unpack <$> TextIO.readFile path),
        hostWriteFile = \path text -> io (TextIO.writeFile path (Text.pack text)),
        hostAppendFile = \path text -> io (TextIO.appendFile path (Text.pack text)),
        hostRandom = (\time -> realToFrac (time - fromInteger (floor time))) <$> getPOSIXTime,
        hostUnixTime = floor <$> getPOSIXTime,
        hostArguments = pure arguments,
        hostEnvironment = lookupEnv,
        hostRunProcess = \command inputs ->
          io (readProcessWithExitCode command inputs "")
            >>= pure . fmap \(status, output, errors) ->
              (case status of ExitSuccess -> 0; ExitFailure code -> toInteger code, output, errors),
        hostFork = \action -> do
          result <- newEmptyMVar
          thread <- forkIO do
            outcome <- try action
            void (tryPutMVar result (either (Left . displayException @SomeException) id outcome))
          atomicModifyIORef' tasks \(next, table) -> ((next + 1, Map.insert next (result, thread) table), next),
        hostWait = \handle -> task handle >>= maybe (pure (Left "unknown task")) (readMVar . fst),
        hostWaitFor = \handle milliseconds ->
          task handle >>= \case
            Nothing -> pure (Just (Left "unknown task"))
            Just (result, _) -> timeout (microseconds milliseconds) (readMVar result),
        hostCancel = \handle ->
          task handle >>= mapM_ \(result, thread) -> do
            killThread thread
            void (tryPutMVar result (Left "task cancelled")),
        hostSleep = threadDelay . microseconds,
        hostServe = \port respond ->
          if port < 1 || port > 65535
            then pure (Left "web port must be between 1 and 65535")
            else either (Left . displayException) Right <$> try @IOException (Web.serve port respond)
      }
  where
    microseconds milliseconds = fromInteger (max 0 (min (toInteger (maxBound :: Int) `div` 1000) milliseconds)) * 1000
    io :: IO a -> IO (Either String a)
    io action = either (Left . displayException) Right <$> try @IOException action

data Runtime
  = RFunction (Runtime -> Either String Runtime)
  | RConstructor SymbolId [Runtime]
  | RLiteral HostLiteral
  | RRecord [(String, Runtime)]
  | RErased
  | -- a failed computation, such as `sorry`, standeth
    -- unused until something inspecteth it.
    RFailure String
  | RDeed Deed
  | RTask Int

-- a deed describeth an action. building or composing one performeth nothing.
data Deed
  = DPure Runtime
  | DBind Runtime Runtime
  | DFix Runtime
  | -- a catalogue deed with its explicit inputs.
    DHost String [Runtime]

-- execution stopth on a failure or an `exit`.
data Stop = Failure String | Exit Integer

type Execution m = ExceptT Stop m

-- a runnable program defineth `main: 𝟙 deed`.
requireMain :: SourceProgram -> Either String ()
requireMain = void . checkedMain "a runnable file"

-- validation and execution share the same checked entry point.
checkedMain :: String -> SourceProgram -> Either String (Globals, SymbolId)
checkedMain caller program = do
  let K.Environment globals = sourceEnvironment program
  name <- maybe (Left (caller ++ " requireth a top-level main")) pure (sourceGlobal program "main")
  Definition {definitionType, definitionBody} <- maybe (Left "main is not a checked definition") pure (Map.lookup name globals)
  case definitionBody of
    Transparent _ -> pure ()
    _ -> Left "main must be a let definition"
  matchMain globals definitionType
  pure (globals, name)

-- main must have a unit deed type. a normal end hath exit status 0.
runMain :: (Monad m) => HostIO m -> SourceProgram -> Either String (m (Either String Integer))
runMain host program = do
  (globals, name) <- checkedMain "program" program
  let table = runtimeGlobals globals
  value <- Lazy.findWithDefault (Left "main is missing") name table
  pure do
    outcome <- runExceptT (execute host value)
    pure case outcome of
      Right _ -> Right 0
      Left (Exit status) -> Right status
      Left (Failure message) -> Left message

-- a yielded judgement is validated before erasure. a yielded deed is
-- performed, as at a repl prompt.
runYield :: (Monad m) => HostIO m -> SourceProgram -> K.Inferred -> m (Either String Runtime)
runYield host program inferred = do
  let K.Environment globals = sourceEnvironment program
      table = runtimeGlobals globals
  case K.validate (sourceEnvironment program) inferred >> evaluate table [] (K.inferredTerm inferred) of
    Left message -> pure (Left message)
    Right value@(RDeed _) ->
      runExceptT (execute host value) <&> \case
        Right result -> Right result
        Left (Failure message) -> Left message
        Left (Exit status) -> Left ("exited with status " ++ show status)
    Right value -> pure (settled value)

-- haskell shareth each delayed computation. a failed one keepeth its failure
-- until inspected, just as an unused argument keepeth its value unevaluated.
delayed :: Either String Runtime -> Runtime
delayed = either RFailure id

inspected :: Runtime -> Either String Runtime
inspected = \case
  RFailure message -> Left message
  value -> Right value

-- observations compute data fully; closures and inert deeds stay opaque.
settled :: Runtime -> Either String Runtime
settled =
  inspected >=> \case
    RConstructor name values -> RConstructor name <$> traverse settled values
    RRecord fields -> RRecord <$> traverse (traverse settled) fields
    RLiteral literal -> rnf literal `seq` pure (RLiteral literal)
    value -> pure value

-- values print as the ordinary evaluator printeth them. erased inputs, such as
-- implicit constructor fields, are not shown.
renderRuntime :: Runtime -> String
renderRuntime = \case
  RLiteral literal -> renderLiteral literal
  RRecord fields -> "r{" ++ intercalate ", " [name ++ " ≔ " ++ renderRuntime value | (name, value) <- sortOn fst fields] ++ "}"
  RConstructor name values -> case [value | value <- values, not (erased value)] of
    [] -> constructorName name
    shown -> "(" ++ unwords (map renderRuntime shown) ++ " " ++ constructorName name ++ ")"
  RFunction _ -> "<function>"
  RErased -> "<erased>"
  RFailure _ -> "<failure>"
  RDeed _ -> "<deed>"
  RTask _ -> "<task>"
  where
    erased = \case
      RErased -> True
      _ -> False
    constructorName = lastQualifiedSegment . symbolName

execute :: (Monad m) => HostIO m -> Runtime -> Execution m Runtime
execute host = \case
  RDeed deed -> case deed of
    -- producers compute data fully, including literal payloads, before a
    -- continuation receiveth it. bind and fix stay in tail position, so a
    -- loop retaineth neither pending arithmetic nor return frames.
    DPure value -> runtime (settled value)
    DBind action continuation -> do
      value <- execute host action
      continue continuation [value]
    DFix step -> continue step [RDeed (DFix step)]
    DHost key arguments -> do
      inputs <- runtime (traverse settled arguments)
      perform host key inputs >>= runtime . settled
  RFailure message -> throwE (Failure message)
  _ -> throwE (Failure "runtime value is not a deed")
  where
    continue function arguments = runtime (foldM apply function arguments) >>= execute host

-- each case followeth the catalogue type of its key. a fallible deed returneth
-- an option or `string ∑ α`, as in the ordinary runner.
perform :: (Monad m) => HostIO m -> String -> [Runtime] -> Execution m Runtime
perform host key arguments = case (key, arguments) of
  ("write", [text -> Just value]) -> lift (hostWrite host value) >>= runtime >> pure only
  ("read", []) -> option . either (const Nothing) (Just . textValue) <$> lift (hostRead host)
  ("random", []) -> RLiteral . FloatBits . castDoubleToWord64 <$> lift (hostRandom host)
  ("unix_time", []) -> RLiteral . IntegerValue <$> lift (hostUnixTime host)
  ("sleep", [natural -> Just milliseconds]) -> lift (hostSleep host milliseconds) >> pure only
  ("fork", [action]) -> RTask <$> lift (hostFork host (taskOutcome <$> runExceptT (execute host action)))
  -- a failed or cancelled task hath no result.
  ("wait", [RTask handle]) -> option . either (const Nothing) Just <$> lift (hostWait host handle)
  ("wait_for", [RTask handle, natural -> Just milliseconds]) -> option . (>>= either (const Nothing) Just) <$> lift (hostWaitFor host handle milliseconds)
  ("outstrike", [RTask handle]) -> lift (hostCancel host handle) >> pure only
  ("read_file", [text -> Just path]) -> outcome textValue <$> lift (hostReadFile host path)
  ("write_file", [text -> Just path, text -> Just value]) -> outcome (const only) <$> lift (hostWriteFile host path value)
  ("athang_file", [text -> Just path, text -> Just value]) -> outcome (const only) <$> lift (hostAppendFile host path value)
  ("arguments", []) -> list . map textValue <$> lift (hostArguments host)
  ("environment", [text -> Just name]) -> option . fmap textValue <$> lift (hostEnvironment host name)
  ("exit", [natural -> Just status]) -> throwE (Exit status)
  ("run_process", [text -> Just command, inputs]) -> do
    texts <- runtime (maybe (Left "process arguments must be string") Right (listed inputs >>= traverse text))
    outcome (\(status, output, errors) -> RConstructor (coreConstructor processResultConstructorId) [RLiteral (IntegerValue status), textValue output, textValue errors])
      <$> lift (hostRunProcess host command texts)
  -- serving endeth with a message when the transport or a handler faileth.
  ("serve", [natural -> Just port, handler]) ->
    lift (hostServe host port (runExceptT . respond)) >>= \case
      Left message -> pure (textValue message)
      Right (Failure message) -> pure (textValue message)
      Right stop -> throwE stop
    where
      respond request = do
        value <- runtime (apply handler (requestValue request)) >>= execute host
        runtime (responseOf value)
  _ -> throwE (Failure ("invalid runtime host call '" ++ key ++ "'"))
  where
    taskOutcome = \case
      Right value -> Right value
      Left (Failure message) -> Left message
      Left (Exit status) -> Left ("task exited with status " ++ show status)
    outcome success = either (\message -> RConstructor (coreConstructor leftConstructorId) [textValue message]) (\value -> RConstructor (coreConstructor rightConstructorId) [success value])

runtime :: (Monad m) => Either String a -> Execution m a
runtime = either (throwE . Failure) pure

text :: Runtime -> Maybe String
text = \case
  RLiteral (TextValue value) -> Just value
  _ -> Nothing

natural :: Runtime -> Maybe Integer
natural = \case
  RLiteral (NaturalValue value) -> Just (toInteger value)
  _ -> Nothing

textValue :: String -> Runtime
textValue = RLiteral . TextValue

only :: Runtime
only = RConstructor (coreConstructor onlyConstructorId) []

option :: Maybe Runtime -> Runtime
option = maybe (RConstructor (coreConstructor noneConstructorId) []) (RConstructor (coreConstructor someConstructorId) . pure)

list :: [Runtime] -> Runtime
list = foldr (\value rest -> RConstructor (coreConstructor consConstructorId) [value, rest]) (RConstructor (coreConstructor emptyConstructorId) [])

listed :: Runtime -> Maybe [Runtime]
listed = \case
  RConstructor constructor []
    | constructor == coreConstructor emptyConstructorId -> Just []
  RConstructor constructor [value, rest]
    | constructor == coreConstructor consConstructorId -> (value :) <$> listed rest
  _ -> Nothing

pair :: Runtime -> Runtime -> Runtime
pair left right = RConstructor (coreConstructor productConstructorId) [left, right]

-- headers cross the boundary as a text table of pairs.
headerTable :: [(Text.Text, Text.Text)] -> Runtime
headerTable headers = RConstructor (coreConstructor tableConstructorId) [list [pair (textValue (Text.unpack name)) (textValue (Text.unpack value)) | (name, value) <- headers]]

requestValue :: Web.Request -> Runtime
requestValue Web.Request {..} =
  RConstructor
    (coreConstructor requestConstructorId)
    [ textValue (Text.unpack requestMethod),
      textValue (Text.unpack requestTarget),
      headerTable requestHeaders,
      textValue (Text.unpack requestBody)
    ]

responseOf :: Runtime -> Either String Web.Response
responseOf = \case
  RConstructor constructor [natural -> Just status, RConstructor table [rows], text -> Just body]
    | constructor == coreConstructor responseConstructorId,
      table == coreConstructor tableConstructorId -> do
        pairs <- maybe (Left "web response inholdeth a non-string header") pure do
          entries <- listed rows
          traverse (\case RConstructor product [text -> Just name, text -> Just value] | product == coreConstructor productConstructorId -> Just (Text.pack name, Text.pack value); _ -> Nothing) entries
        unless (all (\(name, value) -> Web.validHeaderName name && Web.validHeaderValue value) pairs) (Left "invalid response header")
        pure (Web.Response status pairs (Text.pack body))
  _ -> Left "web handler returned an invalid response"

-- pure host values cross by the catalogue's shared shape.
toHostValue :: Runtime -> Maybe HostValue
toHostValue = \case
  RLiteral literal -> Just (literalValue literal)
  value -> HostList <$> (listed value >>= traverse toHostValue)

fromHostValue :: HostValue -> Runtime
fromHostValue = \case
  HostTruth truth -> RConstructor (coreConstructor (if truth then yeaConstructorId else nayConstructorId)) []
  HostOption value -> option (fromHostValue <$> value)
  HostPair left right -> pair (fromHostValue left) (fromHostValue right)
  HostList values -> list (map fromHostValue values)
  value -> maybe RErased RLiteral (valueLiteral value)

-- globals are acyclic, so this lazy table evaluateth each one at most once.
runtimeGlobals :: Globals -> Lazy.Map SymbolId (Either String Runtime)
runtimeGlobals globals = table
  where
    table = Lazy.mapWithKey global globals
    global name Definition {definitionBody} = case definitionBody of
      Transparent term -> evaluate table [] term
      EliminationTarget _ term -> evaluate table [] term
      TypeConstructor _ -> pure RErased
      -- number constructors work on literals.
      DataConstructor _ _
        | Just literal <- constructedLiteral name [] -> pure (RLiteral literal)
        | name `elem` [naturalSuccessorId, integerPositiveId, integerNegativeId] ->
            pure (RFunction \case RLiteral field | Just literal <- constructedLiteral name [field] -> pure (RLiteral literal); RFailure message -> Left message; _ -> Left "a number constructor of a non-literal")
      DataConstructor owner index -> constructor name owner index
      Eliminator family -> eliminator name family
      Host key _ | key `elem` Primitive.opaqueTypeFamilyNames ++ literalTypeNames -> pure RErased
      Host "sorry" _ -> pure (RFunction \_ -> pure (RFailure "reached sorry"))
      Assumption -> pure (RFailure ("reached orsetting '" ++ symbolName name ++ "'"))
      Host "literal_case" _ -> curried 6 \case
        [_, _, actual, expected, yes, no] ->
          traverse inspected [actual, expected] >>= \case
            [RLiteral actual, RLiteral expected] -> inspected (if actual == expected then yes else no)
            _ -> Left "invalid runtime literal case"
        _ -> Left "invalid runtime literal case"
      Host key _ -> host key
    constructor name owner index = do
      (parameters, fields) <- constructorInfo owner index
      curried (parameters + length fields) (pure . RConstructor name . drop parameters)
    constructorInfo owner index = case definitionBody <$> Map.lookup owner globals of
      Just (TypeConstructor InductiveInfo {inductiveParameterCount, inductiveConstructorInfo})
        | (_, fields) : _ <- drop index inductiveConstructorInfo -> pure (inductiveParameterCount, fields)
      _ -> Left "invalid runtime constructor metadata"
    -- both evaluators execute the same checked constructor rule. runtime
    -- constructors have already discarded their original uniform parameters.
    eliminator name family = do
      info@InductiveInfo {..} <- inductiveInfo globals family
      groupMethods <- inductiveMethods globals info
      let prefixSize = inductiveParameterCount + length inductiveFamilies + length groupMethods
          indexCount = length inductiveIndexPlicities
          induct arguments = do
            let (prefix, rest) = splitAt prefixSize arguments
            scrutinee <- case drop indexCount rest of
              [value] -> inspected value
              _ -> Left "invalid runtime induction arguments"
            case literalView scrutinee of
              RConstructor constructorName values
                | Just Definition {definitionBody = DataConstructor owner index} <- Map.lookup constructorName globals,
                  Just row <- if owner == family then Just index else findIndex ((== constructorName) . fst) inductiveConstructorInfo,
                  row >= 0,
                  ((selected, fields), rule) : _ <- drop row (zip inductiveConstructorInfo inductiveRules),
                  selected == constructorName,
                  length fields == length values ->
                    evaluate table (reverse (prefix ++ values)) rule
              RFailure message -> Left message
              _ -> Left ("induction " ++ show name ++ " received a non-constructor")
      curried (prefixSize + indexCount + 1) induct
    literalView = \case
      RLiteral literal | Just (constructor, fields) <- literalConstructor literal -> RConstructor constructor (map RLiteral fields)
      value -> value
    -- type inputs arrive erased before the explicit inputs.
    host key = do
      binding@HostBinding {hostSignature = HostSignature {hostVariables}} <- maybe (Left ("unknown host key '" ++ key ++ "'")) pure (findForeignBinding key)
      curried (length hostVariables + Primitive.hostArity binding) \inputs -> do
        let arguments = drop (length hostVariables) inputs
        case (pureOperation key, key, arguments) of
          (Just operation, _, _) -> do
            values <- traverse settled arguments
            maybe (Left ("invalid runtime host call '" ++ key ++ "'")) (pure . fromHostValue) (traverse toHostValue values >>= operation)
          (_, "deed_sheer", [value]) -> pure (RDeed (DPure value))
          (_, "deed_bind", [action, continuation]) -> pure (RDeed (DBind action continuation))
          (_, "deed_steadfast", [step]) -> pure (RDeed (DFix step))
          _ -> pure (RDeed (DHost key arguments))

-- inputs arrive in order; the body receiveth them once all are present.
curried :: Int -> ([Runtime] -> Either String Runtime) -> Either String Runtime
curried arity body = go arity []
  where
    go 0 arguments = body (reverse arguments)
    go remaining arguments = pure (RFunction \argument -> go (remaining - 1) (argument : arguments))

evaluate :: Lazy.Map SymbolId (Either String Runtime) -> [Runtime] -> Term -> Either String Runtime
evaluate table environment = \case
  Local index -> case drop index environment of
    value : _ -> pure value
    [] -> Left "unbound runtime local"
  Global name _ -> Lazy.findWithDefault (Left "unknown runtime global") name table
  Sort _ -> pure RErased
  Pi {} -> pure RErased
  Lambda _ _ body -> pure (RFunction \argument -> evaluate table (argument : environment) body)
  Apply _ function argument -> evaluate table environment function >>= \functionValue -> apply functionValue (delayed (evaluate table environment argument))
  Let _ value body -> evaluate table (delayed (evaluate table environment value) : environment) body
  Meta {} -> Left "runtime term inholdeth an inference hole"
  Literal _ value -> pure (RLiteral value)
  RecordType _ -> pure RErased
  Record fields -> pure (RRecord [(name, delayed (evaluate table environment field)) | (name, field) <- fields])
  Project record name ->
    evaluate table environment record >>= \case
      RRecord fields | Just value <- lookup name fields -> pure value
      RFailure message -> Left message
      _ -> Left ("runtime projection of a missing field '" ++ name ++ "'")
  Field index value ->
    evaluate table environment value >>= inspected >>= \case
      RConstructor _ fields | field : _ <- drop index fields -> inspected field
      _ -> Left "runtime field of a non-constructor"

apply :: Runtime -> Runtime -> Either String Runtime
apply function argument = case function of
  RFunction body -> body argument
  RErased -> pure RErased
  RFailure message -> Left message
  _ -> Left "runtime application of a non-function"
