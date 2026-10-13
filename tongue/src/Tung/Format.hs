-- | the canonical two-space neatener for the cli and editor. it parseth the
-- source first and refuseth what doth not parse. layout then followeth only
-- the tokens, their brackets, and the comments between them: whitespace in
-- the source never changeth the output, so each concrete syntax tree hath
-- one neat form, and neatening is idempotent.
module Tung.Format (formatSource) where

import Data.Char (isDigit, isSpace)
import Data.IntMap.Strict qualified as IntMap
import Data.List (dropWhileEnd, intercalate, isPrefixOf, sort, sortOn, stripPrefix)
import Data.Maybe (isJust)
import Tung.Dependent.Source.Parse (parseProgram)
import Tung.Token

-- the widest line the neatener leaveth when the line can be broken.
lineLimit :: Int
lineLimit = 80

formatSource :: String -> Either String String
formatSource source = do
  _ <- parseProgram source
  located <- lexLocatedTokens source
  let pieces = attachComments source located
      (declarations, closing) = topLevel (forest pieces)
      rendered = renderDeclarations (sortBrings declarations) closing
      result = intercalate "\n" (alignRows (map (dropWhileEnd isSpace) (lines rendered)))
      output = if null (trim result) then "" else dropWhileEnd (== '\n') result ++ "\n"
  -- the neatener only moveth whitespace and comments, so the tokens agree.
  after <- lexTokens output
  before <- lexTokens source
  if sort (map show after) == sort (map show before)
    then Right output
    else Left "the neatener changed the tokens; this is a compiler fault"

-- a token's own text with the comments before it and the one that endeth its
-- line. a comment on the line of the previous token trails that token; any
-- other leadeth the next. the last piece's leading comments close the file.
data Piece = Piece
  { pieceText :: String,
    pieceToken :: Maybe Token,
    pieceLeading :: [String],
    pieceTrailing :: Maybe String
  }

attachComments :: String -> [LocatedToken] -> [Piece]
attachComments source located = go 0 Nothing located
  where
    characters = utf16Characters source
    character offset = IntMap.findWithDefault (length source) offset characters
    slice from to = take (to - from) (drop from source)
    go from previous = \case
      [] ->
        let (trailing, leading) = gapComments (isJust previous) (drop from source)
         in finish previous trailing ++ [Piece "" Nothing leading Nothing]
      LocatedToken (SourceSpan start end) token : rest ->
        let (trailing, leading) = gapComments (isJust previous) (slice from (character start))
            piece = Piece (slice (character start) (character end)) (Just token) leading Nothing
         in finish previous trailing ++ go (character end) (Just piece) rest
    finish previous trailing = case previous of
      Just piece -> [piece {pieceTrailing = trailing}]
      Nothing -> []

-- utf-16 offsets of token spans as character indices.
utf16Characters :: String -> IntMap.IntMap Int
utf16Characters source = IntMap.fromList (zip (scanl (+) 0 (map width source)) [0 ..])
  where
    width character = if fromEnum character > 0xffff then 2 else 1

-- the comments of the whitespace between two tokens: the one on the earlier
-- token's line, if any, and the others in order.
gapComments :: Bool -> String -> (Maybe String, [String])
gapComments afterToken = go True
  where
    go sameLine text = case dropWhile (\character -> isSpace character && character /= '\n') text of
      [] -> (Nothing, [])
      '\n' : rest -> go False rest
      '#' : rest ->
        let (body, remaining) = break (== '\n') rest
            comment = dropWhileEnd isSpace ('#' : body)
            (trailing, leading) = go False remaining
         in if sameLine && afterToken then (Just comment, trailing `before` leading) else (Nothing, comment : maybe leading (: leading) trailing)
      '/' : '*' : rest ->
        let (body, remaining) = blockComment rest
            comment = "/*" ++ body
            (trailing, leading) = go False remaining
         in if sameLine && afterToken then (Just comment, trailing `before` leading) else (Nothing, comment : maybe leading (: leading) trailing)
      _ : rest -> go sameLine rest
    before trailing leading = maybe leading (: leading) trailing
    blockComment = \case
      '*' : '/' : rest -> ("*/", rest)
      character : rest -> let (body, remaining) = blockComment rest in (character : body, remaining)
      [] -> ([], [])

-- tokens nest by their brackets; `>{` and `<{` open a brace.
data Node = Atom Piece | Bracket Piece [Node] Piece

forest :: [Piece] -> [Node]
forest = fst . go
  where
    go = \case
      [] -> ([], [])
      piece : rest
        | opens piece ->
            let (inside, afterInside) = go rest
             in case afterInside of
                  close : remaining ->
                    let (siblings, final) = go remaining
                     in (Bracket piece inside close : siblings, final)
                  [] -> ([Bracket piece inside (Piece "" Nothing [] Nothing)], [])
        | closes piece -> ([], piece : rest)
        | otherwise -> let (siblings, final) = go rest in (Atom piece : siblings, final)

opens, closes :: Piece -> Bool
opens piece = case pieceToken piece of
  Just token -> token `elem` [TLParen, TLBracket, TLBrace] || isBraceKeyword token
  Nothing -> False
closes piece = maybe False (`elem` [TRParen, TRBracket, TRBrace]) (pieceToken piece)

isBraceKeyword :: Token -> Bool
isBraceKeyword = \case
  TBraceKeyword _ -> True
  _ -> False

-- top-level declarations, and the comments that close the file.
topLevel :: [Node] -> ([[Node]], [String])
topLevel nodes =
  let closing = case reverse nodes of
        Atom piece@Piece {pieceToken = Nothing} : _ -> pieceLeading piece
        _ -> []
      body = [node | node <- nodes, not (endOfFile node)]
   in (splitDeclarations body, closing)
  where
    endOfFile = \case
      Atom Piece {pieceToken = Nothing} -> True
      _ -> False

-- a declaration beginneth at a keyword, except `let` after `show`.
splitDeclarations :: [Node] -> [[Node]]
splitDeclarations = go []
  where
    go current = \case
      [] -> [reverse current | not (null current)]
      node : rest
        | startsDeclaration node, not (null current), not (afterShow current) -> reverse current : go [node] rest
        | otherwise -> go (node : current) rest
    afterShow = \case
      [Atom piece] -> pieceToken piece == Just TExport
      _ -> False

startsDeclaration :: Node -> Bool
startsDeclaration = \case
  Atom piece -> maybe False (`elem` [TLet, TExport, TImport, TType, TClass, TInstance, TOrsend, TYield]) (pieceToken piece)
  _ -> False

-- consecutive `bring` declarations are sorted by path.
sortBrings :: [[Node]] -> [[Node]]
sortBrings = \case
  [] -> []
  declarations@(first : _)
    | bringing first ->
        let (brings, rest) = span bringing declarations
         in sortOn bringKey brings ++ sortBrings rest
  declaration : rest -> declaration : sortBrings rest
  where
    bringKey = map pieceText . concatMap nodePieces

bringing :: [Node] -> Bool
bringing = \case
  Atom piece : _ -> pieceToken piece == Just TImport
  _ -> False

nodePieces :: Node -> [Piece]
nodePieces = \case
  Atom piece -> [piece]
  Bracket open inside close -> open : concatMap nodePieces inside ++ [close]

-- one blank line between declarations, none between `bring`s.
renderDeclarations :: [[Node]] -> [String] -> String
renderDeclarations declarations closing =
  let rendered = [(bringing declaration, layout (declarationDoc declaration)) | declaration <- declarations]
      joined = concat (zipWith separator (Nothing : map (Just . fst) rendered) rendered)
      separator previous (isBring, text) = case previous of
        Nothing -> text
        Just wasBring -> (if wasBring && isBring then "\n" else "\n\n") ++ text
      ending = if null closing then "" else (if null rendered then "" else "\n\n") ++ layout (commentsDoc closing)
   in joined ++ ending

declarationDoc :: [Node] -> Doc
declarationDoc written =
  let (comments, nodes) = hoistLeading written
   in commentsDoc comments <> case (declaresBody nodes, reverse nodes) of
        (True, Bracket open inside close : before)
          | braceLike open ->
              sequenceDoc (reverse before) <> Text " " <> bracketDoc DeclarationBody open inside close
        _ -> itemDoc nodes
  where
    declaresBody = \case
      Atom piece : rest
        | pieceToken piece == Just TExport -> declaresBody rest
        | otherwise -> maybe False (`elem` [TType, TClass, TInstance]) (pieceToken piece)
      _ -> False

-- a brace that holdeth an ilk's constructors, a flock's members, or a
-- bizen's members is a declaration body, and one after `match …` is a match
-- body: both are padded. a declaration body and a case block of more than one
-- row always break.
data Context = Ordinary | DeclarationBody | MatchBody
  deriving (Eq)

-- an item is one slot, row, member, or argument of its bracket. a binding
-- `≔` or a row's `^` keepeth its left side and breaketh before the right one,
-- unless the right side openeth a block.
-- the comments before an item stand at the item's own indentation.
hoistLeading :: [Node] -> ([String], [Node])
hoistLeading = \case
  Atom piece : rest -> (pieceLeading piece, Atom piece {pieceLeading = []} : rest)
  Bracket open inside close : rest -> (pieceLeading open, Bracket open {pieceLeading = []} inside close : rest)
  [] -> ([], [])

itemDoc :: [Node] -> Doc
itemDoc written =
  let (comments, nodes) = hoistLeading written
   in commentsDoc comments <> itemBody nodes

itemBody :: [Node] -> Doc
itemBody nodes
  | Just binding <- bindingDoc nodes = binding
  | otherwise = arrowBody nodes

-- a `let` or `orsetting` that doth not fit on one line putteth its `≔ body`
-- on a line of its own, two columns in, and its `: annotation` too when the
-- name and annotation do not fit together; a block after `≔` openeth on that
-- line.
bindingDoc :: [Node] -> Maybe Doc
bindingDoc nodes = do
  let (keywords, afterKeywords) = span keyword nodes
  name : rest <- Just afterKeywords
  guard (any binds keywords)
  let (annotation, body) = case rest of
        Atom colon : afterColon
          | pieceToken colon == Just TColon -> case splitAtToken TEquals afterColon of
              Just (written, sign, right) -> (Just (colon, written), Just (sign, right))
              Nothing -> (Just (colon, afterColon), Nothing)
        _ -> (Nothing, fmap (\(_, sign, right) -> (sign, right)) (splitAtToken TEquals rest))
      head' = sequenceDoc (keywords ++ [name])
      annotationDoc = case annotation of
        Just (colon, written) -> Nest 2 (SoftLine <> pieceDoc colon <> Text " " <> sequenceDoc written)
        Nothing -> Nil
      named = Group (head' <> annotationDoc)
  -- a body that openeth a block standeth outside the group, so the binding
  -- need fit only up to the block's opening; the block decideth its own form.
  pure case body of
    Just (sign, right)
      | opensBlock right -> Group (named <> Nest 2 (Line <> pieceDoc sign)) <> Text " " <> sequenceDoc right
      | otherwise -> Group (named <> Nest 2 (Line <> pieceDoc sign <> (if null right then Nil else Text " " <> sequenceDoc right)))
    Nothing -> named
  where
    keyword = \case
      Atom piece -> maybe False (`elem` [TExport, TLet, TOrsend]) (pieceToken piece)
      _ -> False
    binds = \case
      Atom piece -> maybe False (`elem` [TLet, TOrsend]) (pieceToken piece)
      _ -> False
    guard condition = if condition then Just () else Nothing

-- a row's `^`, or a binding outside a declaration, keepeth its left side on
-- the line and breaketh before the right one unless that openeth a block.
arrowBody :: [Node] -> Doc
arrowBody nodes = case splitAtToken TEquals nodes of
  Just (left, sign, right) -> sequenceDoc left <> Text " " <> pieceDoc sign <> rightDoc right
  Nothing -> case splitAtToken TMapsTo nodes of
    Just (left, sign, right) -> sequenceDoc left <> Text " " <> pieceDoc sign <> rightDoc right
    Nothing -> sequenceDoc nodes
  where
    rightDoc right
      | null right = Nil
      | opensBlock right = Text " " <> sequenceDoc right
      | otherwise = Group (Nest 2 (Line <> sequenceDoc right))

-- the first top-level occurrence of a token, outside a `match` head.
splitAtToken :: Token -> [Node] -> Maybe ([Node], Piece, [Node])
splitAtToken wanted = go []
  where
    go seen = \case
      [] -> Nothing
      Atom piece : rest | pieceToken piece == Just wanted -> Just (reverse seen, piece, rest)
      node : rest -> go (node : seen) rest

-- a right side that beginneth with a brace, a block of declarations, or a
-- `match` keepeth to the line of its sign.
opensBlock :: [Node] -> Bool
opensBlock = \case
  Bracket open inside _ : _ -> braceLike open || declarationBlock inside
  Atom piece : _ -> pieceToken piece == Just TMatch
  _ -> False

braceLike :: Piece -> Bool
braceLike piece = maybe False (\token -> token == TLBrace || isBraceKeyword token) (pieceToken piece)

declarationBlock :: [Node] -> Bool
declarationBlock = any startsDeclaration

-- terms of one item: each space may break, filling lines, except after `:`
-- and `$`, and there is no space inside a name such as `x.field` or `@α`.
-- a term that doth not fit beginneth a continuation line, two columns in. a
-- `match` head and a brace opening a block stay on the line before them.
sequenceDoc :: [Node] -> Doc
sequenceDoc = go Nothing False
  where
    go _ _ [] = Nil
    go previous matching (node : rest) =
      let context = if matching then MatchBody else Ordinary
          term = nodeDoc context node
          joined = case previous of
            Nothing -> term
            Just earlier
              | glued (lastPiece earlier) (firstPiece node) -> term
              | matching || lastToken earlier `elem` [Just TColon, Just TDollar] || braceLike (firstPiece node) -> Text " " <> term
              | otherwise -> Group (Nest 2 (Line <> term))
          stillMatching = case node of
            Atom piece -> matching || pieceToken piece == Just TMatch
            Bracket open _ _ -> matching && not (braceLike open)
       in joined <> go (Just node) stillMatching rest

nodeDoc :: Context -> Node -> Doc
nodeDoc context = \case
  Atom piece -> pieceDoc piece
  Bracket open inside close -> bracketDoc context open inside close

glued :: Piece -> Piece -> Bool
glued left right =
  maybe False noSpaceAfter (pieceToken left) || maybe False noSpaceBefore (pieceToken right)
  where
    noSpaceAfter token = token `elem` [TLParen, TLBracket, TLBrace, TAt, TDot] || isBraceKeyword token
    noSpaceBefore token = token `elem` [TRParen, TRBracket, TRBrace, TComma, TSemicolon, TColon, TDot]

firstPiece, lastPiece :: Node -> Piece
firstPiece = \case
  Atom piece -> piece
  Bracket open _ _ -> open
lastPiece = \case
  Atom piece -> piece
  Bracket _ _ close -> close

lastToken :: Node -> Maybe Token
lastToken = pieceToken . lastPiece

bracketDoc :: Context -> Piece -> [Node] -> Piece -> Doc
bracketDoc context open inside close
  | null inside = pieceDoc open <> pieceDoc close
  | open `has` TLBracket = pieceDoc open <> Nest 2 (fillItems (items inside)) <> pieceDoc close
  | open `has` TLParen, declarationBlock inside = blockDoc False False (items inside)
  | open `has` TLParen = pieceDoc open <> itemDoc inside <> pieceDoc close
  | maybe False isBraceKeyword (pieceToken open) = case items inside of
      first : rest -> FromLine (Group (pieceDoc open <> itemDoc first <> Nest 2 (mconcat [Line <> itemDoc item | item <- rest]) <> SoftLine <> pieceDoc close))
      [] -> pieceDoc open <> pieceDoc close
  | otherwise =
      let rows = items inside
          padded = context /= Ordinary
          forced = (context == DeclarationBody && (length rows > 1 || declarationBlock inside)) || (isCases rows && length rows > 1)
       in blockDoc padded forced rows
  where
    has piece token = pieceToken piece == Just token
    isCases rows = any (any isCaret) rows || any endsWithSemicolon rows
    isCaret = \case
      Atom piece -> piece `has` TMapsTo
      _ -> False
    endsWithSemicolon row = case reverse row of
      Atom piece : _ -> piece `has` TSemicolon
      _ -> False
    blockDoc padded forced rows =
      let inner = mconcat (zipWith (\index item -> (if index == (0 :: Int) then Nil else Line) <> itemDoc item) [0 ..] rows)
          edge = if padded then Line else SoftLine
          body = pieceDoc open <> Nest 2 (edge <> inner) <> edge <> pieceDoc close
       in FromLine (if forced then Break body else Group body)

-- slots fill their line and wrap where they must.
fillItems :: [[Node]] -> Doc
fillItems = \case
  [] -> Nil
  first : rest -> itemDoc first <> mconcat [Group (Line <> itemDoc item) | item <- rest]

-- the items of a bracket's inside: a `,` or `;` endeth an item, except a `,`
-- between a row's patterns before its `^` and between `match` scrutinees;
-- a declaration keyword beginneth one.
items :: [Node] -> [[Node]]
items = go [] False False
  where
    go current _ _ [] = [reverse current | not (null current)]
    go current caret inMatch (node : rest)
      | startsDeclaration node, not (null current), not (afterShow current) = reverse current : go [node] False False rest
      | isToken TSemicolon node = reverse (node : current) : go [] False False rest
      | isToken TComma node, not inMatch, caret || not (rowAhead rest) = reverse (node : current) : go [] False False rest
      | isToken TMapsTo node = go (node : current) True inMatch rest
      | isToken TMatch node = go (node : current) caret True rest
      | inMatch, isBrace node = go (node : current) caret False rest
      | otherwise = go (node : current) caret inMatch rest
    afterShow = \case
      [Atom piece] -> pieceToken piece == Just TExport
      _ -> False
    isToken token = \case
      Atom piece -> pieceToken piece == Just token
      _ -> False
    isBrace = \case
      Bracket open _ _ -> pieceToken open == Just TLBrace
      _ -> False
    -- a `,` before a `^` of the same row separateth its patterns.
    rowAhead = \case
      [] -> False
      node : rest
        | isToken TMapsTo node -> True
        | isToken TComma node || isToken TSemicolon node -> rowAhead rest
        | startsDeclaration node -> False
        | otherwise -> rowAhead rest

pieceDoc :: Piece -> Doc
pieceDoc Piece {..} =
  commentsDoc pieceLeading <> Text pieceText <> maybe Nil (\comment -> Text " " <> Comment comment <> HardLine) pieceTrailing

commentsDoc :: [String] -> Doc
commentsDoc comments = mconcat [HardLine <> Comment comment <> HardLine | comment <- comments]

-- a document of the kind wadler and leijen describe. a comment endeth its
-- line with a hard line, which a group may hold and still lie flat;
-- consecutive line breaks merge into one.
data Doc
  = Nil
  | Text String
  | Comment String
  | Line
  | SoftLine
  | HardLine
  | Nest Int Doc
  | Group Doc
  | Break Doc
  | -- a block: its inside is indented from the line it beginneth on, so it
    -- closeth at that line's indentation.
    FromLine Doc
  | Doc :<> Doc

instance Semigroup Doc where
  (<>) = (:<>)

instance Monoid Doc where
  mempty = Nil

data Mode = Flat | Broken
  deriving (Eq)

layout :: Doc -> String
layout doc = dropWhileEnd isSpace (go 0 (Just 0) 0 [(0, Broken, doc)])
  where
    -- `pending` is the indentation awaited by a fresh line; consecutive
    -- breaks merge into one, so no break leaveth an empty line. `lineAt` is
    -- the indentation of the line being written.
    go :: Int -> Maybe Int -> Int -> [(Int, Mode, Doc)] -> String
    go _ _ _ [] = ""
    go column pending lineAt ((indent, mode, current) : rest) = case current of
      Nil -> go column pending lineAt rest
      Text "" -> go column pending lineAt rest
      Text text -> start ++ text ++ go (here + length text) Nothing current' rest
      Comment comment ->
        let wrapped = wrapComment (lineLimit - here) comment
         in start ++ intercalate ("\n" ++ replicate here ' ') wrapped ++ go (here + length (last wrapped)) Nothing current' rest
      left :<> right -> go column pending lineAt ((indent, mode, left) : (indent, mode, right) : rest)
      Nest more inner -> go column pending lineAt ((indent + more, mode, inner) : rest)
      FromLine inner -> go column pending lineAt ((current', mode, inner) : rest)
      Line | mode == Flat -> if pending == Nothing then ' ' : go (column + 1) Nothing lineAt rest else go column pending lineAt rest
      SoftLine | mode == Flat -> go column pending lineAt rest
      Group inner
        | mode == Flat -> go column pending lineAt ((indent, Flat, inner) : rest)
        | fits (lineLimit - here) [(indent, Flat, inner)] rest -> go column pending lineAt ((indent, Flat, inner) : rest)
        | otherwise -> go column pending lineAt ((indent, Broken, inner) : rest)
      Break inner -> go column pending lineAt ((indent, Broken, inner) : rest)
      _ -> case pending of
        Just _ -> go column (Just indent) lineAt rest
        Nothing -> '\n' : go column (Just indent) lineAt rest
      where
        here = maybe column id pending
        start = maybe "" (`replicate` ' ') pending
        current' = maybe lineAt id pending
    fits width items rest
      | width < 0 = False
      | otherwise = case items of
          [] -> case rest of
            [] -> True
            next : others -> fits width [next] others
          (indent, mode, current) : others -> case current of
            Nil -> fits width others rest
            Text text -> fits (width - length text) others rest
            Comment comment -> fits (width - length comment) others rest
            left :<> right -> fits width ((indent, mode, left) : (indent, mode, right) : others) rest
            Nest more inner -> fits width ((indent + more, mode, inner) : others) rest
            FromLine inner -> fits width ((indent, mode, inner) : others) rest
            Line | mode == Flat -> fits (width - 1) others rest
            SoftLine | mode == Flat -> fits width others rest
            Group inner -> fits width ((indent, mode, inner) : others) rest
            Break inner -> fits width ((indent, Broken, inner) : others) rest
            -- what followeth a comment's line end must fit the next line.
            HardLine -> fits (lineLimit - indent) others rest
            _ -> True

-- a comment wider than its room breaketh at its last fitting space, keeping
-- its marker; a block comment is never broken.
wrapComment :: Int -> String -> [String]
wrapComment room comment
  | length comment <= room || "/*" `isPrefixOf` comment = [comment]
  | otherwise =
      let marker = if "##" `isPrefixOf` comment then "##" else "#"
          text = dropWhile isSpace (drop (length marker) comment)
          lead = marker ++ " "
          spaces = [index | (index, ' ') <- zip [0 ..] text, index > 0, length lead + index <= room]
       in case spaces of
            [] -> [comment]
            _ ->
              let position = last spaces
               in (lead ++ take position text) : wrapComment room (lead ++ dropWhile isSpace (drop position text))

-- consecutive case rows of one indentation with as many pattern columns
-- align: each column is padded after its comma, and `^` followeth the widest
-- last column. a `;` alternative is a row without a result. rows that would
-- grow wider than the limit are left unaligned.
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
              aligned = map (renderRow (widths group)) group
              original = take (length group) lines'
           in (if all ((<= lineLimit) . length) aligned then aligned else original) ++ go Code remaining
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
  guard' (not (null content) && not (commentHead content) && not (declarationHead content))
  (patterns, result) <- split 0 [] content
  let columns = map trim (topLevelCommas patterns)
  guard' (not (null patterns) && all (not . null) columns && all (not . any (`elem` ("≔{" :: String))) columns)
  pure (CaseRow indent columns (fmap trim result))
  where
    guard' condition = if condition then Just () else Nothing
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

data LexicalState = Code | Text' | BlockComment

lineLexicalState :: LexicalState -> String -> LexicalState
lineLexicalState = go
  where
    go state [] = case state of
      Text' -> Code
      _ -> state
    go BlockComment ('*' : '/' : rest) = go Code rest
    go BlockComment (_ : rest) = go BlockComment rest
    go Text' ('\\' : _ : rest) = go Text' rest
    go Text' ('\'' : rest) = go Code rest
    go Text' (_ : rest) = go Text' rest
    go Code ('#' : _) = Code
    go Code ('/' : '*' : rest) = go BlockComment rest
    go Code ('\'' : rest) = go Text' rest
    go Code ('`' : rest) = go Code (characterLiteralTail rest)
    go Code (_ : rest) = go Code rest

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace

declarationHead :: String -> Bool
declarationHead line = any (`startsHead` line) ["bring", "yield", "show", "let", "ilk", "flock", "bizen", "orsetting"]

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
