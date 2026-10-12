-- | authoritative two-space formatting for the cli and editor. the formatter
-- is structural so comments and incomplete source survive without parsing or
-- type checking; formatting is idempotent.
module Tung.Format (formatSource) where

import Control.Monad (guard)
import Data.Char (isDigit, isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf, isSuffixOf, mapAccumL, sortOn, stripPrefix)

-- each indentation level holdeth the brackets one line opened, so a line
-- opening `(match x {` indenteth its body once, not twice.
data FormatState = FormatState
  { formatDepth :: !Int,
    formatGroups :: ![Int],
    formatLexicalState :: !LexicalState,
    formatContinuation :: !Int,
    formatContinuationBlocks :: ![(Int, Int)],
    -- structural base depth and unmatched square brackets in a split header.
    formatHeaderBracket :: !(Maybe (Int, Int))
  }

data LexicalState = Code | Text | BlockComment

formatSource :: String -> String
formatSource source =
  let (_, formatted) = mapAccumL formatLine initialState (sortUseBlocks (sourceLines source))
      result = intercalate "\n" (alignRows formatted)
   in if "\n" `isSuffixOf` source
        then dropWhileEnd (== '\n') result ++ "\n"
        else result

-- consecutive case rows of one indentation with as many pattern columns
-- align: each column is padded after its comma, and `^` followeth the widest
-- last column. a `;` alternative is a row without a result.
data CaseRow = CaseRow
  { rowIndent :: String,
    rowColumns :: [String],
    rowResult :: Maybe String
  }

alignRows :: [String] -> [String]
alignRows = go Code
  where
    go _ [] = []
    go Code lines'@(line : _)
      | Just row <- caseRow line =
          let (group, remaining) = spanRows row lines'
           in map (renderRow (widths group)) group ++ go Code remaining
    go lexicalState (line : rest) = line : go (lineLexicalState lexicalState line) rest
    spanRows first = \case
      line : rest
        | Just row <- caseRow line,
          rowIndent row == rowIndent first,
          length (rowColumns row) == length (rowColumns first) ->
            let (group, remaining) = spanRows first rest in (row : group, remaining)
      remaining -> ([], remaining)
    widths group = foldr1 (zipWith max) [map length (rowColumns row) | row <- group]
    renderRow columnWidths CaseRow {..} =
      let padded = [column ++ "," ++ replicate (width - length column + 1) ' ' | (column, width) <- zip (init rowColumns) columnWidths]
          final = last rowColumns
       in rowIndent ++ concat padded ++ case rowResult of
            Just result -> final ++ replicate (last columnWidths - length final) ' ' ++ " ^" ++ (if null result then "" else ' ' : result)
            Nothing -> final ++ ";"

-- a line whose own top level holdeth `^`, or that endeth in `;`, outside
-- brackets, literals, and comments.
caseRow :: String -> Maybe CaseRow
caseRow line = do
  let (indent, content) = span (== ' ') line
  guard (not (null content) && not (commentHead content) && not (declarationHead content))
  (patterns, result) <- split 0 [] content
  let columns = map trim (topLevelCommas patterns)
  guard (not (null patterns) && all (not . null) columns && all (not . any (`elem` ("≔{" :: String))) columns)
  pure (CaseRow indent columns (fmap trim result))
  where
    split :: Int -> String -> String -> Maybe (String, Maybe String)
    split depth seen = \case
      [] | depth == 0, ';' : before <- seen -> Just (reverse before, Nothing)
      [] -> Nothing
      '\'' : rest -> literal ('\'' : seen) rest >>= \(seen', rest') -> split depth seen' rest'
      '`' : rest ->
        let remaining = characterLiteralTail rest
         in split depth (reverse (take (length rest - length remaining) rest) ++ '`' : seen) remaining
      '#' : _ -> Nothing
      '^' : rest | depth == 0 -> Just (reverse seen, Just rest)
      character : rest
        | character `elem` ("([{" :: String) -> split (depth + 1) (character : seen) rest
        | character `elem` (")]}" :: String) -> if depth == 0 then Nothing else split (depth - 1) (character : seen) rest
        | otherwise -> split depth (character : seen) rest
    literal seen = \case
      '\\' : character : rest -> literal (character : '\\' : seen) rest
      '\'' : rest -> Just ('\'' : seen, rest)
      character : rest -> literal (character : seen) rest
      [] -> Nothing
    topLevelCommas = go' 0 []
      where
        go' :: Int -> String -> String -> [String]
        go' _ current [] = [reverse current]
        go' depth current (character : rest)
          | character == ',' && depth == 0 = reverse current : go' depth [] rest
          | character `elem` ("([{" :: String) = go' (depth + 1) (character : current) rest
          | character `elem` (")]}" :: String) = go' (depth - 1) (character : current) rest
          | otherwise = go' depth (character : current) rest

initialState :: FormatState
initialState = FormatState 0 [] Code 0 [] Nothing

sortUseBlocks :: [String] -> [String]
sortUseBlocks = go Code
  where
    go _ [] = []
    go Code lines'@(line : rest)
      | sortableUseLine line =
          let (uses, remaining) = span sortableUseLine lines'
           in sortOn trim uses ++ go Code remaining
      | otherwise = line : go (lineLexicalState Code line) rest
    go lexicalState (line : rest) = line : go (lineLexicalState lexicalState line) rest

    sortableUseLine line =
      let content = trim line
       in startsWord "use" content && case lineLexicalState Code content of
            Code -> True
            _ -> False

lineLexicalState :: LexicalState -> String -> LexicalState
lineLexicalState lexicalState line =
  let (_, _, next, _, _) = scanLine lexicalState line
   in next

formatLine :: FormatState -> String -> (FormatState, String)
formatLine state@FormatState {formatLexicalState = BlockComment} line =
  let (_, _, lexicalState, _, _) = scanLine BlockComment line
   in (state {formatLexicalState = lexicalState}, line)
formatLine state line
  | null content =
      let continuation = case formatHeaderBracket state of
            Just (base, count) -> max 0 (count - (formatDepth state - base))
            Nothing -> 0
       in (state {formatContinuation = continuation}, "")
  | otherwise =
      let closes = leadingClosures content
          startsDeclaration = declarationHead content
          startsComment = commentHead content
          lineContinuation
            | closes > 0 || startsDeclaration || startsComment = 0
            | formatHeaderBracket state /= Nothing && "]" `isPrefixOf` content = max 0 (formatContinuation state - 1)
            -- a top-level line that is no declaration head continueth the
            -- previous declaration, as a body after `] ≔ {...}` doth.
            | formatDepth state == 0 && formatHeaderBracket state == Nothing && not ("]" `isPrefixOf` content) = max 1 (formatContinuation state)
            | otherwise = formatContinuation state
          lineDepth = max 0 (formatDepth state - closedLevels closes (formatGroups state) + lineContinuation)
          (rawDelta, bracketDelta, lexicalState, code, content) = scanned
          groups = openGroups (rawDelta + closes) (closeGroups closes (formatGroups state))
          delta = length groups - length (formatGroups state)
          oldDepth = formatDepth state
          -- a continued line opening a block keepeth its continuation, unless
          -- it closeth a header bracket, as `@a:*, head] {` doth.
          continuedBlock = lineContinuation > 0 && delta > 0 && not headerClosed
          balancedDepth = max 0 (oldDepth + delta + if continuedBlock then lineContinuation else 0)
          blocks =
            if continuedBlock
              then (oldDepth + lineContinuation, lineContinuation) : formatContinuationBlocks state
              else formatContinuationBlocks state
          (depth, remainingBlocks) = if delta < 0 then releaseBlocks balancedDepth blocks else (balancedDepth, blocks)
          headerBracket = case formatHeaderBracket state of
            Just (base, count) | count + bracketDelta > 0 -> Just (base, count + bracketDelta)
            Just _ -> Nothing
            Nothing
              | bracketDelta > 0
                  && any (`startsHead` code) ["let", "show let", "bizen", "flock", "show flock", "orsetting", "show orsetting"]
                  && '≔' `notElem` code ->
                  Just (oldDepth, bracketDelta)
            Nothing -> Nothing
          headerClosed = case formatHeaderBracket state of
            Just _ -> headerBracket == Nothing
            Nothing -> False
          continuation
            | startsComment = formatContinuation state
            | headerClosed = if any (`isSuffixOf` code) ["]", "≔"] then 1 else 0
            | Just (base, count) <- headerBracket = max 0 (count - (depth - base))
            | "≔" `isSuffixOf` code = 1
            | closes > 0 = 0
            -- a trailing comma endeth a row or item, and with it its continuation.
            | "," `isSuffixOf` code = 0
            | delta == 0 && lineContinues code (lineContinuation > 0) = 1
            | lineContinuation > 0 && delta == 0 = max 2 lineContinuation
            | otherwise = 0
          next = FormatState depth groups lexicalState continuation remainingBlocks headerBracket
       in (next, replicate (lineDepth * 2) ' ' ++ content)
  where
    scanned@(_, _, _, _, content) = scanLine (formatLexicalState state) (trim line)

-- the levels that leading closures reach, partly or fully: a line beginning
-- `}}` under `({s ^ >{` returneth to the level of the line that opened them.
closedLevels :: Int -> [Int] -> Int
closedLevels count groups
  | count <= 0 = 0
closedLevels count (open : rest)
  | count <= open = 1
  | otherwise = 1 + closedLevels (count - open) rest
closedLevels _ [] = 0

closeGroups :: Int -> [Int] -> [Int]
closeGroups count groups
  | count <= 0 = groups
closeGroups count (open : rest)
  | count < open = (open - count) : rest
  | otherwise = closeGroups (count - open) rest
closeGroups _ [] = []

-- a net opening becometh one level; a net closing closeth older levels.
openGroups :: Int -> [Int] -> [Int]
openGroups change groups
  | change > 0 = change : groups
  | otherwise = closeGroups (negate change) groups

releaseBlocks :: Int -> [(Int, Int)] -> (Int, [(Int, Int)])
releaseBlocks depth blocks@((closingDepth, extraDepth) : rest)
  | closingDepth == depth = releaseBlocks (max 0 (depth - extraDepth)) rest
  | otherwise = (depth, blocks)
releaseBlocks depth [] = (depth, [])

sourceLines :: String -> [String]
sourceLines = map (dropWhileEnd (== '\r')) . lines

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace

leadingClosures :: String -> Int
leadingClosures = length . takeWhile (`elem` ("})" :: String))

declarationHead :: String -> Bool
declarationHead line = any (`startsHead` line) ["use", "yield", "show", "let", "ilk", "flock", "bizen", "orsetting"]

commentHead :: String -> Bool
commentHead line = "#" `isPrefixOf` line || "/*" `isPrefixOf` line

-- a declaration keyword is followed by a space or, for `bizen`, ':'.
startsHead :: String -> String -> Bool
startsHead word line = startsWord word line || (word ++ ":") `isPrefixOf` line

startsWord :: String -> String -> Bool
startsWord word line = case stripPrefix word line of
  Just [] -> True
  Just (next : _) -> isSpace next
  Nothing -> False

-- a line ending in `≔` or a row's `^` continueth on the next line.
lineContinues :: String -> Bool -> Bool
lineContinues code continued =
  "≔" `isSuffixOf` code
    || "^" `isSuffixOf` code
    || (continued && ":" `isPrefixOf` code)

-- one tolerant scan preserveth quoted text and comments while collecting
-- layout and compacting type colons. code after a block comment affecteth
-- depth, but not the line's continuation marker.
scanLine :: LexicalState -> String -> (Int, Int, LexicalState, String, String)
scanLine started input =
  let (delta, bracketDelta, lexicalState, code, output) = go 0 0 started True [] [] input
   in (delta, bracketDelta, lexicalState, dropWhileEnd isSpace (reverse code), reverse output)
  where
    go delta brackets lexicalState _ code output [] = (delta, brackets, lexicalState, code, output)
    go delta brackets BlockComment collect code output ('*' : '/' : rest) = go delta brackets Code collect code ('/' : '*' : output) rest
    go delta brackets BlockComment collect code output (character : rest) = go delta brackets BlockComment collect code (character : output) rest
    go delta brackets Text collect code output ('\\' : character : rest) = go delta brackets Text collect code (character : '\\' : output) rest
    go delta brackets Text collect code output ('\'' : rest) = go delta brackets Code collect code ('\'' : output) rest
    go delta brackets Text collect code output (character : rest) = go delta brackets Text collect code (character : output) rest
    go delta brackets Code _ code output ('#' : rest) = (delta, brackets, Code, code, reverse rest ++ '#' : output)
    go delta brackets Code _ code output ('/' : '*' : rest) = go delta brackets BlockComment False code ('*' : '/' : output) rest
    go delta brackets Code collect code output ('\'' : rest) = go delta brackets Text collect code ('\'' : output) rest
    go delta brackets Code collect code output ('`' : rest) =
      let remaining = characterLiteralTail rest
          literal = take (length rest - length remaining) rest
       in go delta brackets Code collect code (reverse literal ++ '`' : output) remaining
    go delta brackets Code collect code output (':' : rest) =
      let following = dropWhile isSpace rest
          spaced = case following of
            [] -> False
            next : _ -> next `notElem` ",]"
          suffix = if spaced then " :" else ":"
          -- only output whitespace immediately before the colon is removed.
          removed = length (takeWhile isSpace output)
          prefix = if collect then drop removed code else code
          nextCode = if collect then suffix ++ prefix else code
       in go delta brackets Code collect nextCode (suffix ++ dropWhile isSpace output) following
    go delta brackets Code collect code output (character : rest) =
      let depthChange = if character `elem` ("{(" :: String) then 1 else if character `elem` ("})" :: String) then -1 else 0
          bracketChange = if character == '[' then 1 else if character == ']' then -1 else 0
          nextCode = if collect then character : code else code
       in go (delta + depthChange) (brackets + bracketChange) Code collect nextCode (character : output) rest

characterLiteralTail :: String -> String
characterLiteralTail [] = []
characterLiteralTail ('\\' : rest) = case rest of
  [] -> []
  first : remaining
    | isDigit first ->
        let (_, afterDigits) = span isDigit rest
         in case afterDigits of
              ';' : after -> after
              _ -> afterDigits
    | otherwise -> remaining
characterLiteralTail (_ : rest) = rest
