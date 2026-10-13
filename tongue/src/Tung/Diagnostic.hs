{-# LANGUAGE OverloadedStrings #-}

-- | structured source diagnostics for command-line and editor clients.
module Tung.Diagnostic
  ( Diagnostic (..),
    DiagnosticKind (..),
    failureDiagnostic,
    renderFileDiagnostic,
  )
where

import Data.Aeson (ToJSON (..), object, (.=))
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Tung.Dependent.Source (CompileFailure (..), FailureKind (..))
import Tung.Token (SourceSpan (..))

data DiagnosticKind = ParseDiagnostic | TypeDiagnostic | GoalDiagnostic
  deriving (Eq, Show)

data Diagnostic = Diagnostic
  { diagnosticKind :: !DiagnosticKind,
    diagnosticPath :: Maybe FilePath,
    diagnosticSpan :: !SourceSpan,
    diagnosticMessage :: String
  }
  deriving (Eq, Show)

instance ToJSON Diagnostic where
  toJSON Diagnostic {diagnosticKind, diagnosticPath, diagnosticSpan = SourceSpan start end, diagnosticMessage} =
    object
      ( [ "kind" .= renderKind diagnosticKind,
          "start" .= start,
          "end" .= end,
          "message" .= diagnosticMessage
        ]
          ++ maybe [] (\path -> ["path" .= path]) diagnosticPath
      )

-- a dependent compile failure, located in the module that raised it. an
-- unlocated infrastructure failure useth the start of that module's source.
failureDiagnostic :: String -> Map.Map String String -> CompileFailure -> Diagnostic
failureDiagnostic source imports CompileFailure {failureKind, failurePath, failureSpan, failureText} =
  let owner = maybe source (\path -> Map.findWithDefault source path imports) failurePath
      (kind, prefix) = case failureKind of
        ParseFailure -> (ParseDiagnostic, "parse error: ")
        CheckFailure -> (TypeDiagnostic, "ilk error: ")
   in Diagnostic kind failurePath (fromMaybe (SourceSpan 0 (min 1 (utf16Length owner))) failureSpan) (prefix ++ failureText)

renderFileDiagnostic :: FilePath -> String -> Diagnostic -> String
renderFileDiagnostic path source Diagnostic {diagnosticSpan = SourceSpan start end, diagnosticMessage} =
  intercalate ":" [path, show startLine, show startColumn, show endLine, show endColumn] ++ ": " ++ diagnosticMessage
  where
    (startLine, startColumn) = sourcePosition source start
    (endLine, endColumn) = sourcePosition source end

sourcePosition :: String -> Int -> (Int, Int)
sourcePosition source wanted = go 0 1 1 source
  where
    go _ line column [] = (line, column)
    go offset line column _ | offset >= wanted = (line, column)
    go offset line _ ('\n' : rest) = go (offset + 1) (line + 1) 1 rest
    go offset line column (character : rest) =
      let width = utf16Width character
       in go (offset + width) line (column + width) rest

renderKind :: DiagnosticKind -> String
renderKind ParseDiagnostic = "parse"
renderKind TypeDiagnostic = "ilk"
renderKind GoalDiagnostic = "goal"

utf16Length :: String -> Int
utf16Length = sum . map utf16Width

-- a character outside the basic plane is a surrogate pair.
utf16Width :: Char -> Int
utf16Width character = if fromEnum character > 0xffff then 2 else 1
