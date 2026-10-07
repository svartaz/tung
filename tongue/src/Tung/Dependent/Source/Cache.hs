{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | checked module interfaces on disk. a key hasheth a module's source, the
-- keys of its imports, and the compiler build, so an interface is reused only
-- when nothing it was checked from hath changed.
module Tung.Dependent.Source.Cache
  ( cacheKeys,
    compilerBuild,
    loadInterfaces,
    saveInterfaces,
  )
where

import Control.Exception (SomeException, evaluate, try)
import Data.Binary (Binary (..), decodeFileOrFail, encodeFile)
import Data.Bits (xor)
import Data.Char (ord)
import Data.Functor ((<&>))
import Data.List (sort)
import Data.Map.Lazy qualified as Lazy
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Numeric (showHex)
import System.Directory (createDirectoryIfMissing, doesFileExist, getModificationTime, renameFile)
import System.Environment (getExecutablePath)
import System.FilePath ((<.>), (</>))
import Tung.Dependent.Check (Environment (..), Inferred (..))
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Parse (SourceSnapshot (..))
import Tung.Dependent.Source.Syntax (Declaration (..))
import Tung.Dependent.Syntax
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Token (SourceSpan (..))

deriving stock instance Generic ModuleId

deriving stock instance Generic SourceSpan

deriving stock instance Generic HostLiteral

deriving stock instance Generic Level

deriving stock instance Generic Constraint

deriving stock instance Generic Plicity

deriving stock instance Generic Term

deriving stock instance Generic InductiveInfo

deriving stock instance Generic DefinitionBody

deriving stock instance Generic Definition

deriving stock instance Generic Environment

deriving stock instance Generic Inferred

deriving stock instance Generic NameBinding

deriving stock instance Generic Names

deriving stock instance Generic ClassInfo

deriving stock instance Generic Hole

deriving stock instance Generic SourceProgram

instance Binary ModuleId

instance Binary SourceSpan

instance Binary HostLiteral

instance Binary Level

instance Binary Constraint

instance Binary Plicity

instance Binary Term

instance Binary InductiveInfo

instance Binary DefinitionBody

instance Binary Definition

instance Binary Environment

instance Binary Inferred

instance Binary NameBinding

instance Binary Names

instance Binary ClassInfo

instance Binary Hole

instance Binary SourceProgram

-- the hash is rebuilt from the name when an identity is read.
instance Binary SymbolId where
  put (SymbolId owner name) = put owner >> put name
  get = SymbolId <$> get <*> get

-- fnv-1a over the characters, as a hexadecimal word.
fingerprint :: String -> String
fingerprint text = showHex (fromIntegral (foldl' (\hash character -> (hash `xor` fromIntegral (ord character)) * 1099511628211) (14695981039346656037 :: Integer) text `mod` (2 ^ (64 :: Int))) :: Integer) ""

-- each module's key, from its text and its imports' keys. a module whose
-- imports are missing or cyclic hath no key and is never cached.
cacheKeys :: String -> Map.Map String SourceSnapshot -> Map.Map String String
cacheKeys build modules = Map.mapMaybe id candidates
  where
    -- the map is lazy in its values, so a key may consult its imports' keys.
    candidates = Lazy.mapWithKey key modules
    key path snapshot = do
      imports <- importsOf snapshot
      importKeys <- traverse (\imported -> if imported == path then Nothing else Map.lookup imported candidates >>= id) imports
      pure (fingerprint (build ++ "\0" ++ path ++ "\0" ++ snapshotText snapshot ++ "\0" ++ concat (sort importKeys)))

importsOf :: SourceSnapshot -> Maybe [String]
importsOf snapshot = case snapshotProgram snapshot of
  Right (declarations, _) -> Just [importPath | (_, ImportDeclaration {importPath}) <- declarations]
  Left _ -> Nothing

interfacePath :: FilePath -> String -> FilePath
interfacePath directory key = directory </> key <.> "interface"

-- an interface holdeth what importers read: the module's own definitions and
-- its exports. its environment is rebuilt from its imports' interfaces.
data Interface = Interface (Map.Map SymbolId Definition) Names
  deriving stock (Generic)

instance Binary Interface

-- every module whose interface, and whose imports' interfaces, are on disk.
-- an unreadable file is ignored.
loadInterfaces :: FilePath -> Map.Map String SourceSnapshot -> Map.Map String String -> IO (Map.Map String SourceProgram)
loadInterfaces directory modules keys = do
  read' <- Map.fromList . concat <$> traverse load (Map.toList keys)
  -- a lazy map, so each environment shareth its imports' environments.
  let programs = Lazy.mapWithKey (rebuild programs) read'
  pure (Map.mapMaybe id programs)
  where
    load (path, key) = do
      let file = interfacePath directory key
      present <- doesFileExist file
      if not present then pure [] else either (const []) id <$> (try (readInterface path file) :: IO (Either SomeException [(String, Interface)]))
    readInterface path file =
      decodeFileOrFail file >>= \case
        Left _ -> pure []
        Right interface -> [(path, interface)] <$ evaluate interface
    rebuild programs path (Interface own exports) = do
      imports <- Map.lookup path modules >>= importsOf
      environments <- traverse (\imported -> Map.lookup imported programs >>= id <&> \program -> case programEnvironment program of Environment globals -> globals) imports
      pure (SourceProgram (Environment (Map.unions (own : H.primitiveDefinitions : environments))) [] exports Set.empty exports [])

-- each newly checked interface is written beside the others; a failure to
-- write leaveth the cache as it was.
saveInterfaces :: FilePath -> Map.Map String String -> Map.Map String SourceProgram -> IO ()
saveInterfaces directory keys programs = do
  createDirectoryIfMissing True directory
  mapM_ save [(key, path, program) | (path, program) <- Map.toList programs, Just key <- [Map.lookup path keys]]
  where
    save (key, path, program) = do
      let file = interfacePath directory key
          temporary = file <.> "partial"
          Environment globals = programEnvironment program
          own = Map.filterWithKey (\symbol _ -> symbolModule symbol == SourceModule path) globals
      present <- doesFileExist file
      if present
        then pure ()
        else () <$ (try (encodeFile temporary (Interface own (programExports program)) >> renameFile temporary file) :: IO (Either SomeException ()))

-- the running compiler's identity: its path and modification time.
compilerBuild :: IO String
compilerBuild = do
  executable <- getExecutablePath
  modified <- getModificationTime executable
  pure (executable ++ show modified)
