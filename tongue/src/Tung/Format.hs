-- | the canonical two-space neatener for the cli and editor. it parseth the
-- source first and refuseth what doth not parse. it shorteneth each redundant
-- η-expansion, `{a ^ a f}` to `f`, and droppeth redundant parentheses. layout
-- then followeth only the tokens, their brackets, and the comments between
-- them: whitespace in the source never changeth the output, so each concrete
-- syntax tree hath one neat form, and neatening is idempotent.
module Tung.Format (formatSource) where

import Control.Applicative ((<|>))
import Control.Monad (guard)
import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf, nub, sort, sortOn)
import Data.Maybe (fromMaybe, isNothing, listToMaybe)
import Tung.Concrete (Leaf (..), NodeKind (..), Tree (..))
import Tung.Dependent.Source.Parse (parseProgram, sourceTree)
import Tung.Token hiding (Piece (..), PieceKind (..), Placement (..))
import Tung.Token qualified as T

-- the widest line the neatener leaveth when the line can be broken.
lineLimit :: Int
lineLimit = 80

formatSource :: String -> Either String String
formatSource written = do
  _ <- parseProgram written
  let source = shorten written
      (declarations, closing) = topLevel (sourceTree source)
      rendered = renderDeclarations (sortBrings declarations) closing
      result = intercalate "\n" (alignRows (map (dropWhileEnd blank) (outLines rendered)))
      output = if all isSpace result then "" else dropWhileEnd (== '\n') result ++ "\n"
  -- layout only moveth whitespace and comments, so the tokens agree.
  after <- lexTokens output
  before <- lexTokens source
  if sort (map show after) == sort (map show before)
    then Right output
    else Left "the neatener changed the tokens; this is a compiler fault"

-- shortening rewriteth tokens before layout: η-expansions and redundant
-- parentheses, until neither applieth, as dropping one may expose the other.
shorten :: String -> String
shorten written = let once = shortenParens (shortenEta written) in if once == written then written else shorten once

-- a lambda whose binders are its body's last arguments is η-expanded:
-- `{a₁, …, aₙ ^ a₁ f a₂ … aₙ}` is `f`, and `{b ^ m tweak b}` is `m tweak`,
-- parenthesised unless the lambda is a whole expression. its
-- binders are distinct bare names, the rest is names and literals that never
-- name a binder, and no comment standeth inside. an annotated binder keepeth
-- its expansion, as elaboration may need it. the neatener readeth no names,
-- so a binder may be a constructor; a one-row match on one then checketh only
-- when that constructor is its ilk's sole, nullary one, and the shortened
-- function agreeth with it on every input. a shortening may complete an
-- outer one, so it is repeated.
shortenEta :: String -> String
shortenEta source = maybe source (shortenEta . concatMap T.pieceText) (rewrite [] (T.lexPieces source))
  where
    -- the lexemes before the brace, nearest first.
    rewrite before pieces = case pieces of
      [] -> Nothing
      opening@T.Piece {T.pieceKind = T.Lexeme TLBrace} : rest
        | not (matchRows before),
          (inside, T.Piece {T.pieceKind = T.Lexeme TRBrace} : after) <- break closing rest,
          all spaceOrLexeme inside,
          Just kept <- reduced [(token, T.pieceText piece) | piece@T.Piece {T.pieceKind = T.Lexeme token} <- inside] ->
            let alone = wholeExpression before after
                text = case kept of
                  [single] -> single
                  _ | alone -> unwords kept
                  _ -> "(" ++ unwords kept ++ ")"
             in Just (opening {T.pieceText = text} : after)
      first : rest -> (first :) <$> rewrite (lexemes first ++ before) rest
    -- `match scrutinees {rows}`: its brace holdeth rows, not a function.
    matchRows = (== Just TMatch) . listToMaybe . dropWhile (`notElem` (TMatch : expressionStarts))
    closing = \case
      T.Piece {T.pieceKind = T.Lexeme token} -> token `elem` [TLBrace, TRBrace]
      _ -> False
    -- the written tokens that remain, or nothing when the lambda is needed.
    reduced written = do
      let tokens = map fst written
      (header, TMapsTo : body) <- Just (break (== TMapsTo) tokens)
      binders <- names header
      guard ("_" `notElem` binders && nub binders == binders)
      let bound = map TIdent binders
          count = length binders
          offset = length header + 1
          texts = map snd (drop offset written)
          free = all (`notElem` bound)
      case body of
        -- every argument is a binder: `a₁ f a₂ … aₙ` is `f`.
        first : function@(TIdent _) : others
          | first : others == bound, free [function] -> Just [texts !! 1]
        _
          | length body - count >= 2,
            drop (length body - count) body == bound,
            all atomic (take (length body - count) body),
            free (take (length body - count) body) ->
              Just (take (length body - count) texts)
        _ -> Nothing
    atomic = \case
      TIdent "_" -> False
      TKindStar -> False
      TSorry -> False
      token -> literalOrName token
    names = \case
      [TIdent name] -> Just [name]
      TIdent name : TComma : rest -> (name :) <$> names rest
      _ -> Nothing

-- parentheses are redundant where the parse cannot change: around one atom,
-- a name, literal, or bracketed group, unless `@(…)` writeth an implicit
-- argument or a `:` or `.` followeth; and around a run of atoms that is a
-- whole expression. a comment inside keepeth them, and each becometh a space,
-- so no tokens join.
shortenParens :: String -> String
shortenParens source = maybe source (shortenParens . concatMap T.pieceText) (strip [] (T.lexPieces source))
  where
    strip before pieces = case pieces of
      [] -> Nothing
      opening@T.Piece {T.pieceKind = T.Lexeme TLParen} : rest
        | (inside, closer@T.Piece {T.pieceKind = T.Lexeme TRParen} : after) <- matching 0 rest,
          all spaceOrLexeme inside,
          Just items <- atoms (concatMap lexemes inside),
          redundant before after items ->
            let space piece = piece {T.pieceText = " ", T.pieceKind = T.Space}
             in Just (space opening : inside ++ space closer : after)
      first : rest -> (first :) <$> strip (lexemes first ++ before) rest
    redundant before after = \case
      [_] -> listToMaybe before /= Just TAt && listToMaybe (concatMap lexemes after) `notElem` [Just TColon, Just TDot]
      _ : _ : _ -> wholeExpression before after
      [] -> False
    -- the pieces before the bracket that closeth this depth, and the rest.
    matching :: Int -> [T.Piece] -> ([T.Piece], [T.Piece])
    matching depth pieces = case pieces of
      [] -> ([], [])
      piece : rest
        | depth == 0, closes piece -> ([], pieces)
        | otherwise ->
            let (inner, outer) = matching (depth + fromEnum (opens piece) - fromEnum (closes piece)) rest
             in (piece : inner, outer)
    opens = any opener . lexemes
    closes = any closer . lexemes
    opener token = token `elem` [TLParen, TLBracket, TLBrace] || isBraceKeyword token
    closer token = token `elem` [TRParen, TRBracket, TRBrace]
    -- the top-level items of a run, each an atom or a bracketed group.
    atoms tokens = case tokens of
      [] -> Just []
      token : rest
        | literalOrName token -> (() :) <$> atoms rest
        | opener token -> (() :) <$> (atoms =<< afterGroup (0 :: Int) rest)
        | otherwise -> Nothing
    afterGroup depth = \case
      [] -> Nothing
      token : rest
        | closer token -> if depth == 0 then Just rest else afterGroup (depth - 1) rest
        | opener token -> afterGroup (depth + 1) rest
        | otherwise -> afterGroup depth rest

-- a whole expression followeth one of these, or `yield`, and precedeth a
-- closing bracket, a separator, the next declaration, or the end.
expressionStarts :: [Token]
expressionStarts = [TLParen, TLBracket, TLBrace, TComma, TMapsTo, TEquals, TSemicolon]

wholeExpression :: [Token] -> [T.Piece] -> Bool
wholeExpression before after =
  maybe False (`elem` (TYield : expressionStarts)) (listToMaybe before)
    && maybe True (`elem` ends) (listToMaybe (concatMap lexemes after))
  where
    ends = [TRParen, TRBracket, TRBrace, TComma, TSemicolon, TLet, TFix, TExport, TType, TClass, TInstance, TOrsend, TImport, TYield]

lexemes :: T.Piece -> [Token]
lexemes = \case
  T.Piece {T.pieceKind = T.Lexeme token} -> [token]
  _ -> []

spaceOrLexeme :: T.Piece -> Bool
spaceOrLexeme = \case
  T.Piece {T.pieceKind = T.Space} -> True
  T.Piece {T.pieceKind = T.Lexeme _} -> True
  _ -> False

literalOrName :: Token -> Bool
literalOrName = \case
  TIdent _ -> True
  TNatural _ -> True
  TInteger _ -> True
  TFloat _ -> True
  TUnicode _ -> True
  TText _ -> True
  TKindStar -> True
  TSorry -> True
  _ -> False

-- a token's own text with the comments before it and the one that endeth its
-- line, as the concrete tree attacheth them.
data Piece = Piece
  { pieceText :: String,
    pieceToken :: Maybe Token,
    pieceLeading :: [String],
    pieceTrailing :: Maybe String,
    -- zero-width tags around the text, which mark case rows for alignment.
    pieceBefore :: [Tag],
    pieceAfter :: [Tag]
  }

piece :: Leaf -> Piece
piece Leaf {..} = Piece (maybe "" T.pieceText leafPiece) (leafPiece >>= token) (comments leafLeading) (listToMaybe (comments leafTrailing)) [] []
  where
    token T.Piece {pieceKind = T.Lexeme lexeme} = Just lexeme
    token _ = Nothing
    comments pieces = [dropWhileEnd isSpace (T.pieceText comment) | comment@T.Piece {pieceKind = T.Comment _} <- pieces]

-- a bracket's inside is its items, each with the separator that endeth it:
-- the slots, rows, members, or declarations the parser marked, or else the
-- whole inside as one item.
data Node = Atom Piece | Bracket Piece Inside Piece

data Inside = Inside
  { insideItems :: [[Node]],
    -- the inside holdeth declarations, as a block or a flock's members.
    insideDeclares :: Bool,
    -- the inside holdeth case rows.
    insideRows :: Bool
  }

-- top-level declarations, and the comments that close the file.
topLevel :: Tree -> ([[Node]], [String])
topLevel = \case
  TreeNode FileNode children -> ([nodes declaration | TreeNode DeclarationNode declaration <- children], [comment | TreeLeaf leaf@Leaf {leafPiece = Nothing} <- children, comment <- pieceLeading (piece leaf)])
  tree -> ([nodes [tree]], [])

nodes :: [Tree] -> [Node]
nodes = concatMap \case
  TreeLeaf leaf -> [Atom (piece leaf)]
  TreeNode BracketNode (TreeLeaf open : rest)
    | not (null rest), TreeLeaf close <- last rest -> [Bracket (piece open) (inside (init rest)) (piece close)]
  TreeNode _ children -> nodes children

inside :: [Tree] -> Inside
inside children
  | any marked children = Inside (concatMap expand (go children)) (any (kind DeclarationNode) children) (any (kind RowNode) children)
  | otherwise = Inside [nodes children | not (null children)] False False
  where
    -- each marked child, with the separators after it.
    go = \case
      [] -> []
      child : rest -> let (after, others) = break marked rest in (kind RowNode child, nodes (child : after)) : go others
    expand (row, item) = if row then map tagRow (filter (not . null) (split item)) else [item]
    marked child = any (`kind` child) [DeclarationNode, ItemNode, RowNode]
    kind wanted = \case
      TreeNode found _ -> found == wanted
      _ -> False
    -- a row's `;` endeth one alternative and beginneth the next.
    split = \case
      [] -> []
      item ->
        let (alternative, rest) = break (atomIn [TSemicolon]) item
         in case rest of
              semicolon : after -> (alternative ++ [semicolon]) : split after
              [] -> [alternative]

-- a row's columns end at its pattern commas, and its patterns end before
-- `^` or `;`; the tags let alignment find them in the laid-out lines.
tagRow :: [Node] -> [Node]
tagRow item = case break (atomIn [TMapsTo]) item of
  (left@(_ : _), caret : right) -> start (columns (tagLast ResultStart left)) ++ caret : right
  _ -> case reverse item of
    semicolon : before@(_ : _) | atomIn [TSemicolon] semicolon -> start (columns (tagLast AlternativeEnd (reverse before))) ++ [semicolon]
    _ -> item
  where
    columns = map \node -> if atomIn [TComma] node then after ColumnEnd node else node
    start = \case
      Atom piece : rest -> Atom piece {pieceBefore = RowStart : pieceBefore piece} : rest
      Bracket open contents close : rest -> Bracket open {pieceBefore = RowStart : pieceBefore open} contents close : rest
      [] -> []
    tagLast tag nodes' = case reverse nodes' of
      final : before -> reverse before ++ [after tag final]
      [] -> []
    after tag = \case
      Atom piece -> Atom piece {pieceAfter = pieceAfter piece ++ [tag]}
      Bracket open contents close -> Bracket open contents close {pieceAfter = pieceAfter close ++ [tag]}

-- an atom that is one of these tokens.
atomIn :: [Token] -> Node -> Bool
atomIn tokens = \case
  Atom piece -> maybe False (`elem` tokens) (pieceToken piece)
  _ -> False

isBraceKeyword :: Token -> Bool
isBraceKeyword = \case
  TBraceKeyword _ -> True
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
  node : _ -> atomIn [TImport] node
  _ -> False

nodePieces :: Node -> [Piece]
nodePieces = \case
  Atom piece -> [piece]
  Bracket open Inside {insideItems} close -> open : concatMap (concatMap nodePieces) insideItems ++ [close]

-- one blank line between declarations, none between `bring`s.
renderDeclarations :: [[Node]] -> [String] -> [Out]
renderDeclarations declarations closing =
  let rendered = [(bringing declaration, layout (declarationDoc declaration)) | declaration <- declarations]
      joined = concat (zipWith separator (Nothing : map (Just . fst) rendered) rendered)
      separator previous (isBring, text) = case previous of
        Nothing -> text
        Just wasBring -> map Out (if wasBring && isBring then "\n" else "\n\n") ++ text
      ending = if null closing then [] else map Out (if null rendered then "" else "\n\n") ++ layout (commentsDoc closing)
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
      node : rest -> if atomIn [TExport] node then declaresBody rest else atomIn [TType, TClass, TInstance] node
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

-- a `let`, `fast`, or `orsetting` that doth not fit on one line putteth its `≔ body`
-- on a line of its own, two columns in, and its `: annotation` too when the
-- name and annotation do not fit together; a block after `≔` openeth on that
-- line.
bindingDoc :: [Node] -> Maybe Doc
bindingDoc nodes = do
  let (keywords, afterKeywords) = span (atomIn [TExport, TLet, TFix, TOrsend]) nodes
  name : rest <- Just afterKeywords
  guard (any (atomIn [TLet, TFix, TOrsend]) keywords)
  let (annotation, body) = case rest of
        Atom colon : afterColon
          | pieceToken colon == Just TColon -> case splitAtToken TEquals afterColon of
              Just (written, sign, right) -> (Just (colon, written), Just (sign, right))
              Nothing -> (Just (colon, afterColon), Nothing)
        _ -> (Nothing, fmap (\(_, sign, right) -> (sign, right)) (splitAtToken TEquals rest))
      named = Group (sequenceDoc (keywords ++ [name]) <> foldMap (\(colon, written) -> Nest 2 (SoftLine <> pieceDoc colon <> Text " " <> sequenceDoc written)) annotation)
  -- a body that openeth a block standeth outside the group, so the binding
  -- need fit only up to the block's opening; the block decideth its own form.
  pure case body of
    Just (sign, right)
      | opensBlock right -> Group (named <> Nest 2 (Line <> pieceDoc sign)) <> Text " " <> sequenceDoc right
      | otherwise -> Group (named <> Nest 2 (Line <> pieceDoc sign <> (if null right then Nil else Text " " <> sequenceDoc right)))
    Nothing -> named

-- a row's `^`, or a binding outside a declaration, keepeth its left side on
-- the line and breaketh before the right one unless that openeth a block.
arrowBody :: [Node] -> Doc
arrowBody nodes = case splitAtToken TEquals nodes <|> splitAtToken TMapsTo nodes of
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
  Bracket open inside _ : _ -> braceLike open || insideDeclares inside
  node : _ -> atomIn [TMatch] node
  _ -> False

braceLike :: Piece -> Bool
braceLike piece = maybe False (\token -> token == TLBrace || isBraceKeyword token) (pieceToken piece)

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
              | matching || pieceToken (lastPiece earlier) `elem` [Just TColon, Just TDollar] || braceLike (firstPiece node) -> Text " " <> term
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

bracketDoc :: Context -> Piece -> Inside -> Piece -> Doc
bracketDoc context open Inside {..} close
  | null insideItems = pieceDoc open <> pieceDoc close
  | open `has` TLBracket = pieceDoc open <> Nest 2 (fillItems insideItems) <> pieceDoc close
  | open `has` TLParen, insideDeclares = blockDoc False False
  | open `has` TLParen = pieceDoc open <> itemDoc (concat insideItems) <> pieceDoc close
  | maybe False isBraceKeyword (pieceToken open),
    first : rest <- insideItems =
      FromLine (Group (pieceDoc open <> itemDoc first <> Nest 2 (mconcat [Line <> itemDoc item | item <- rest]) <> SoftLine <> pieceDoc close))
  | otherwise = blockDoc (context /= Ordinary) ((context == DeclarationBody && (several || insideDeclares)) || (insideRows && several))
  where
    has piece token = pieceToken piece == Just token
    several = length insideItems > 1
    blockDoc padded forced =
      let inner = mconcat (zipWith (\index item -> (if index == (0 :: Int) then Nil else Line) <> itemDoc item) [0 ..] insideItems)
          edge = if padded then Line else SoftLine
          body = pieceDoc open <> Nest 2 (edge <> inner) <> edge <> pieceDoc close
       in FromLine (if forced then Break body else Group body)

-- slots fill their line and wrap where they must.
fillItems :: [[Node]] -> Doc
fillItems = \case
  [] -> Nil
  first : rest -> itemDoc first <> mconcat [Group (Line <> itemDoc item) | item <- rest]

pieceDoc :: Piece -> Doc
pieceDoc Piece {..} =
  commentsDoc pieceLeading <> foldMap Marker pieceBefore <> Text pieceText <> foldMap Marker pieceAfter <> maybe Nil (\comment -> Text " " <> Comment comment <> HardLine) pieceTrailing

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
  | Marker Tag
  | Doc :<> Doc

instance Semigroup Doc where
  (<>) = (:<>)

instance Monoid Doc where
  mempty = Nil

data Mode = Flat | Broken
  deriving (Eq)

-- laid-out text with the zero-width tags that mark case rows.
data Out = Out Char | Tag Tag

data Tag = RowStart | ColumnEnd | ResultStart | AlternativeEnd
  deriving (Eq)

blank :: Out -> Bool
blank = \case
  Out character -> isSpace character
  Tag _ -> True

outLines :: [Out] -> [[Out]]
outLines outs = case break (\case Out '\n' -> True; _ -> False) outs of
  (line, _ : rest) -> line : outLines rest
  (line, []) -> [line]

layout :: Doc -> [Out]
layout doc = dropWhileEnd blank (go 0 (Just 0) 0 [(0, Broken, doc)])
  where
    -- `pending` is the indentation awaited by a fresh line; consecutive
    -- breaks merge into one, so no break leaveth an empty line. `lineAt` is
    -- the indentation of the line being written.
    go :: Int -> Maybe Int -> Int -> [(Int, Mode, Doc)] -> [Out]
    go _ _ _ [] = []
    go column pending lineAt ((indent, mode, current) : rest) = case current of
      Nil -> go column pending lineAt rest
      Text "" -> go column pending lineAt rest
      Text text -> map Out (start ++ text) ++ go (here + length text) Nothing current' rest
      Comment comment ->
        let wrapped = wrapComment (lineLimit - here) comment
         in map Out (start ++ intercalate ("\n" ++ replicate here ' ') wrapped) ++ go (here + length (last wrapped)) Nothing current' rest
      Marker tag -> Tag tag : go column pending lineAt rest
      left :<> right -> go column pending lineAt ((indent, mode, left) : (indent, mode, right) : rest)
      Nest more inner -> go column pending lineAt ((indent + more, mode, inner) : rest)
      FromLine inner -> go column pending lineAt ((current', mode, inner) : rest)
      Line | mode == Flat -> if isNothing pending then Out ' ' : go (column + 1) Nothing lineAt rest else go column pending lineAt rest
      SoftLine | mode == Flat -> go column pending lineAt rest
      Group inner
        | mode == Flat -> go column pending lineAt ((indent, Flat, inner) : rest)
        | fits (lineLimit - here) [(indent, Flat, inner)] rest -> go column pending lineAt ((indent, Flat, inner) : rest)
        | otherwise -> go column pending lineAt ((indent, Broken, inner) : rest)
      Break inner -> go column pending lineAt ((indent, Broken, inner) : rest)
      _ -> case pending of
        Just _ -> go column (Just indent) lineAt rest
        Nothing -> Out '\n' : go column (Just indent) lineAt rest
      where
        here = fromMaybe column pending
        start = maybe "" (`replicate` ' ') pending
        current' = fromMaybe lineAt pending
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
            Marker _ -> fits width others rest
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

alignRows :: [[Out]] -> [String]
alignRows = \case
  [] -> []
  lines'@(line : rest)
    | Just row <- caseRow line ->
        let (group, remaining) = spanRows row lines'
            aligned = map (renderRow (widths group)) group
            original = map plain (take (length group) lines')
         in (if all ((<= lineLimit) . length) aligned then aligned else original) ++ alignRows remaining
    | otherwise -> plain line : alignRows rest
  where
    plain line = [character | Out character <- line]
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

-- a line that holdeth one whole row from its start.
caseRow :: [Out] -> Maybe CaseRow
caseRow line = do
  let (lead, content) = span blank line
  (columns, ending) <- case [() | Tag RowStart <- lead] of
    [_] -> columnsOf [] content
    _ -> Nothing
  pure (CaseRow [character | Out character@' ' <- lead] columns ending)
  where
    text outs = trim [character | Out character <- outs]
    columnsOf done outs = case break (\case Tag tag -> tag `elem` [ColumnEnd, ResultStart, AlternativeEnd]; _ -> False) outs of
      (column, Tag ColumnEnd : rest) -> columnsOf (done ++ [dropWhileEnd (== ',') (text column)]) rest
      (column, Tag ResultStart : rest) -> Just (done ++ [text column], Just (trim (drop 1 (text rest))))
      (column, Tag AlternativeEnd : _) -> Just (done ++ [text column], Nothing)
      _ -> Nothing

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace
