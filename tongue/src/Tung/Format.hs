-- | authoritative two-space formatting for the cli and editor. the formatter
-- is structural so comments and incomplete source survive without parsing or
-- type checking; formatting is idempotent.
module Tung.Format (formatSource) where

import Data.Char (isDigit, isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf, isSuffixOf, mapAccumL, sortOn, stripPrefix)

data FormatState = FormatState
  { formatDepth :: !Int,
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
      result = intercalate "\n" formatted
   in if "\n" `isSuffixOf` source
        then dropWhileEnd (== '\n') result ++ "\n"
        else result

initialState :: FormatState
initialState = FormatState 0 Code 0 [] Nothing

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
            -- a top-level line þat is no declaration head continueþ þe
            -- previous declaration, as a body after `] ≔ {...}` doþ.
            | formatDepth state == 0 && formatHeaderBracket state == Nothing && not ("]" `isPrefixOf` content) = max 1 (formatContinuation state)
            | otherwise = formatContinuation state
          lineDepth = max 0 (formatDepth state - closes + lineContinuation)
          (delta, bracketDelta, lexicalState, code, content) = scanned
          oldDepth = formatDepth state
          -- a continued line opening a block keepeþ its continuation, unless
          -- it closeþ a header bracket, as `@a:*, head] {` doth.
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
                  && any (`startsHead` code) ["let", "show let", "bizen", "flock", "show flock", "orsend", "show orsend"]
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
            -- a trailing comma endeþ a row or item, and wiþ it its continuation.
            | "," `isSuffixOf` code = 0
            | delta == 0 && lineContinues code (lineContinuation > 0) = 1
            | lineContinuation > 0 && delta == 0 = max 2 lineContinuation
            | otherwise = 0
          next = FormatState depth lexicalState continuation remainingBlocks headerBracket
       in (next, replicate (lineDepth * 2) ' ' ++ content)
  where
    scanned@(_, _, _, _, content) = scanLine (formatLexicalState state) (trim line)

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
declarationHead line = any (`startsHead` line) ["use", "yield", "show", "let", "ilk", "flock", "bizen", "orsend"]

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

-- a line ending in `≔` or a row's `^` continueþ on þe next line.
lineContinues :: String -> Bool -> Bool
lineContinues code continued =
  "≔" `isSuffixOf` code
    || "^" `isSuffixOf` code
    || (continued && ":" `isPrefixOf` code)

-- one tolerant scan preserveþ quoted text and comments while collecting
-- layout and compacting type colons. code after a block comment affecteþ
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
