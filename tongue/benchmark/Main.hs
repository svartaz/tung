module Main (main) where

import Control.Exception qualified as Exception
import Control.Monad (forM, replicateM, unless, void)
import Data.Foldable (asum)
import Data.List (find, intercalate, sort)
import Data.Map.Strict qualified as Map
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats (RTSStats (allocated_bytes, max_mem_in_use_bytes), getRTSStats, getRTSStatsEnabled)
import System.Directory (doesFileExist, getCurrentDirectory)
import System.Environment (getArgs, getExecutablePath)
import System.Exit (ExitCode (ExitFailure, ExitSuccess), die)
import System.FilePath (takeDirectory, (</>))
import System.Mem (performMajorGC)
import System.Process (readProcessWithExitCode)
import Text.Printf (printf)
import Text.Read (readMaybe)
import Tung
import Tung.Dependent (Inferred)
import Tung.Dependent.Run (ioHost, renderRuntime, requireMain, runMain, runYield)
import Tung.Dependent.Source (CompileFailure (..), SourceProgram, compileSnapshot, sourceDefinitions, sourceSnapshot)

data Config = Config
  { configRuns :: Int,
    configSize :: Int
  }

data BenchmarkCase
  = GeneratedCompile
  | GeneratedEvaluate
  | FibonacciCompile
  | FizzbuzzCompile
  | FizzbuzzEvaluate
  | LambdaCompile
  | LambdaEvaluate
  deriving stock (Bounded, Enum, Eq, Show)

data Sample = Sample
  { sampleElapsedNs :: Word64,
    sampleAllocatedBytes :: Word64,
    samplePeakMemoryBytes :: Word64
  }

data SourceBundle = SourceBundle
  { bundleSource :: String,
    bundleImports :: Map.Map String String
  }

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["--sample", name, "--size", sizeText] -> do
      benchmarkCase <- parseCase name
      size <- positiveInteger "size" sizeText
      runChild benchmarkCase size
    _ -> do
      Config {configRuns, configSize} <- parseConfig arguments
      runParent configRuns configSize

parseConfig :: [String] -> IO Config
parseConfig = go (Config 3 1000)
  where
    go config [] = pure config
    go config ("--runs" : value : rest) = do
      runs <- positiveInteger "runs" value
      go config {configRuns = runs} rest
    go config ("--size" : value : rest) = do
      size <- positiveInteger "size" value
      go config {configSize = size} rest
    go _ _ = die "usage: tung-benchmark [--runs positive-integer] [--size positive-integer]"

positiveInteger :: String -> String -> IO Int
positiveInteger label value = case readMaybe value of
  Just number | number > 0 -> pure number
  _ -> die (label ++ " must be a positive integer")

runParent :: Int -> Int -> IO ()
runParent runs size = do
  executable <- getExecutablePath
  putStrLn ("tung benchmark: " ++ show runs ++ " runs, " ++ show size ++ " generated declarations")
  putStrLn "case                       runs    median ms       min ms  median allocated mib   median peak memory mib"
  rows <- forM allCases \benchmarkCase -> do
    samples <- replicateM runs (readChild executable benchmarkCase size)
    pure (benchmarkCase, samples)
  mapM_ printRow rows

allCases :: [BenchmarkCase]
allCases = [minBound .. maxBound]

readChild :: FilePath -> BenchmarkCase -> Int -> IO Sample
readChild executable benchmarkCase size = do
  (exitCode, output, errors) <-
    readProcessWithExitCode executable ["--sample", caseName benchmarkCase, "--size", show size] ""
  case exitCode of
    ExitSuccess -> case findSample benchmarkCase output of
      Just sample -> pure sample
      Nothing -> die ("benchmark child returned no sample for " ++ caseName benchmarkCase ++ ":\n" ++ output)
    ExitFailure code ->
      die
        ( "benchmark child failed for "
            ++ caseName benchmarkCase
            ++ " with exit "
            ++ show code
            ++ ":\n"
            ++ errors
            ++ output
        )

findSample :: BenchmarkCase -> String -> Maybe Sample
findSample benchmarkCase = asum . map (parseSample benchmarkCase) . lines

parseSample :: BenchmarkCase -> String -> Maybe Sample
parseSample benchmarkCase line = case splitTabs line of
  ["tung-benchmark-sample", name, elapsed, allocated, peak]
    | name == caseName benchmarkCase ->
        Sample <$> readMaybe elapsed <*> readMaybe allocated <*> readMaybe peak
  _ -> Nothing

splitTabs :: String -> [String]
splitTabs value = case break (== '\t') value of
  (field, []) -> [field]
  (field, _ : rest) -> field : splitTabs rest

printRow :: (BenchmarkCase, [Sample]) -> IO ()
printRow (benchmarkCase, samples) =
  printf
    "%-26s %4d %12.3f %12.3f %21.3f %21.3f\n"
    (caseName benchmarkCase)
    (length samples)
    (nanosecondsToMilliseconds (median (sampleElapsedNs <$> samples)))
    (nanosecondsToMilliseconds (minimum (sampleElapsedNs <$> samples)))
    (bytesToMebibytes (median (sampleAllocatedBytes <$> samples)))
    (bytesToMebibytes (median (samplePeakMemoryBytes <$> samples)))

median :: [Word64] -> Word64
median values = sort values !! (length values `div` 2)

nanosecondsToMilliseconds :: Word64 -> Double
nanosecondsToMilliseconds value = fromIntegral value / 1000000

bytesToMebibytes :: Word64 -> Double
bytesToMebibytes value = fromIntegral value / (1024 * 1024)

runChild :: BenchmarkCase -> Int -> IO ()
runChild benchmarkCase size = do
  enabled <- getRTSStatsEnabled
  unless enabled (die "rts statistics are disabled; run the benchmark with +RTS -T")
  action <- prepareAction benchmarkCase size
  performMajorGC
  before <- getRTSStats
  started <- getMonotonicTimeNSec
  action
  finished <- getMonotonicTimeNSec
  performMajorGC
  after <- getRTSStats
  putStrLn
    ( intercalate
        "\t"
        [ "tung-benchmark-sample",
          caseName benchmarkCase,
          show (finished - started),
          show (allocated_bytes after - allocated_bytes before),
          show (max_mem_in_use_bytes after)
        ]
    )

prepareAction :: BenchmarkCase -> Int -> IO (IO ())
prepareAction benchmarkCase size = case benchmarkCase of
  GeneratedCompile -> pure (compileAndForce False (generatedBundle size))
  GeneratedEvaluate -> evaluateAction False (generatedBundle size)
  FibonacciCompile -> compileAndForce True <$> loadByspel "benchmark/fibonacci.tung"
  FizzbuzzCompile -> compileAndForce True <$> loadByspel "byspel/fizzbuzz.tung"
  FizzbuzzEvaluate -> loadByspel "byspel/fizzbuzz.tung" >>= evaluateAction True
  LambdaCompile -> compileAndForce True <$> loadByspel "byspel/lambda.tung"
  LambdaEvaluate -> loadByspel "byspel/lambda.tung" >>= evaluateAction True

generatedBundle :: Int -> SourceBundle
generatedBundle size =
  SourceBundle
    { bundleSource =
        unlines
          ( ["let value0:ℤ ≔ +0"]
              ++ ["let value" ++ show index ++ ":ℤ ≔ +" ++ show index | index <- [1 .. size - 1]]
              ++ ["yield value" ++ show (size - 1)]
          ),
      bundleImports = Map.empty
    }

loadByspel :: FilePath -> IO SourceBundle
loadByspel relativePath = do
  root <- findRepositoryRoot
  roots <- resolveLibraryRoots (root </> relativePath) >>= either die pure
  loaded <- loadProjectFile roots (root </> relativePath)
  case loaded of
    Left message -> die ("could not load " ++ relativePath ++ ": " ++ message)
    Right project -> pure (SourceBundle (projectSource project) (projectImports project))

findRepositoryRoot :: IO FilePath
findRepositoryRoot = getCurrentDirectory >>= search
  where
    search directory = do
      hathBenchmark <- doesFileExist (directory </> "benchmark/fibonacci.tung")
      hathCabal <- doesFileExist (directory </> "tongue/tung.cabal")
      if hathBenchmark && hathCabal
        then pure directory
        else
          let parent = takeDirectory directory
           in if parent == directory
                then die "could not find the tung repository root"
                else search parent

compileAndForce :: Bool -> SourceBundle -> IO ()
compileAndForce runnable bundle = compileBundle runnable bundle >>= forceCore

evaluateAction :: Bool -> SourceBundle -> IO (IO ())
evaluateAction runnable bundle = do
  (program, yielded) <- compileBundle runnable bundle
  forceCore (program, yielded)
  host <- ioHost []
  if runnable
    then case runMain host program of
      Left message -> die message
      Right action -> pure (action >>= either die (\status -> unless (status == 0) (die ("main exited wiþ " ++ show status))))
    else case yielded of
      Nothing -> die "benchmark source yieldeþ no value"
      Just inferred -> pure do
        result <- runYield host program inferred >>= either die pure
        void (Exception.evaluate (length (renderRuntime result)))

compileBundle :: Bool -> SourceBundle -> IO (SourceProgram, Maybe Inferred)
compileBundle runnable SourceBundle {bundleSource, bundleImports} =
  case compileSnapshot Map.empty (SourceModule "benchmark.tung") (sourceSnapshot bundleSource) (Map.map sourceSnapshot bundleImports) of
    Left failure -> die ("benchmark compilation failed: " ++ failureText failure)
    Right compiled@(program, _) -> case if runnable then () <$ requireMain program else Right () of
      Left message -> die message
      Right () -> pure compiled

forceCore :: (SourceProgram, Maybe Inferred) -> IO ()
forceCore (program, yielded) = void (Exception.evaluate (length (show (sourceDefinitions program, yielded))))

caseName :: BenchmarkCase -> String
caseName benchmarkCase = case benchmarkCase of
  GeneratedCompile -> "generated/compile"
  GeneratedEvaluate -> "generated/evaluate"
  FibonacciCompile -> "fibonacci/compile"
  FizzbuzzCompile -> "fizzbuzz/compile"
  FizzbuzzEvaluate -> "fizzbuzz/evaluate"
  LambdaCompile -> "lambda/compile"
  LambdaEvaluate -> "lambda/evaluate"

parseCase :: String -> IO BenchmarkCase
parseCase name = case find ((== name) . caseName) allCases of
  Just benchmarkCase -> pure benchmarkCase
  Nothing -> die ("unknown benchmark case '" ++ name ++ "'")
