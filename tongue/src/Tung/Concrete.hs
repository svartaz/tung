-- | the lossless concrete syntax tree. it endeth in the lexer's pieces, so
-- the tree's text is the source's text. brackets pair lexically; declarations,
-- items, and rows are the spans the parser marked; a region the parser could
-- not read is a broken node. the neatener and editor read this one tree.
module Tung.Concrete
  ( Tree (..),
    Leaf (..),
    NodeKind (..),
    concreteTree,
    treeText,
    treeSpan,
  )
where

import Data.List (sortOn)
import Data.Ord (Down (..))
import Tung.Token

-- a token with the trivia before it and the comment that endeth its line. a
-- leaf without a token holdeth the trivia after the last token.
data Leaf = Leaf
  { leafLeading :: [Piece],
    leafPiece :: Maybe Piece,
    leafTrailing :: [Piece]
  }
  deriving (Eq, Show)

data Tree = TreeLeaf Leaf | TreeNode NodeKind [Tree]
  deriving (Eq, Show)

data NodeKind = FileNode | DeclarationNode | ItemNode | RowNode | BracketNode | BrokenNode
  deriving (Eq, Show)

treeText :: Tree -> String
treeText = \case
  TreeLeaf Leaf {..} -> concatMap pieceText (leafLeading ++ maybe [] pure leafPiece ++ leafTrailing)
  TreeNode _ children -> concatMap treeText children

-- the span from a tree's first token to its last, without trivia.
treeSpan :: Tree -> Maybe SourceSpan
treeSpan tree = case tokenSpans tree of
  [] -> Nothing
  spans@(first : _) -> Just (SourceSpan (spanStart first) (spanEnd (last spans)))
  where
    tokenSpans = \case
      TreeLeaf Leaf {leafPiece = Just piece} -> [pieceSpan piece]
      TreeLeaf _ -> []
      TreeNode _ children -> concatMap tokenSpans children

-- the marks are node spans from the parser; a mark that doth not cover whole
-- siblings is left out. a mark covering a whole bracket's inside nesteth in it.
concreteTree :: [Piece] -> [(NodeKind, SourceSpan)] -> Tree
concreteTree pieces marks = TreeNode FileNode (nest ordered (brackets (leaves pieces)))
  where
    ordered = sortOn (\(kind, SourceSpan start end) -> (start, Down end, kindRank kind)) [mark | mark@(_, SourceSpan start end) <- marks, end > start]
    kindRank = \case
      BrokenNode -> 0 :: Int
      DeclarationNode -> 1
      RowNode -> 2
      _ -> 3

-- each token taketh the trivia before it, and its line's trailing comment.
leaves :: [Piece] -> [Tree]
leaves = go []
  where
    go leading = \case
      [] -> [TreeLeaf (Leaf (reverse leading) Nothing []) | not (null leading)]
      piece : rest
        | trivia piece -> go (piece : leading) rest
        | otherwise ->
            let (trailing, following) = case span (\next -> pieceKind next == Space && '\n' `notElem` pieceText next) rest of
                  (spaces, comment@Piece {pieceKind = Comment Trailing} : after) -> (spaces ++ [comment], after)
                  _ -> ([], rest)
             in TreeLeaf (Leaf (reverse leading) (Just piece) trailing) : go [] following
    trivia Piece {pieceKind} = case pieceKind of
      Space -> True
      Comment _ -> True
      _ -> False

-- brackets pair by their tokens; an unmatched one stayeth a plain leaf.
brackets :: [Tree] -> [Tree]
brackets = fst . go Nothing
  where
    go closing = \case
      [] -> ([], [])
      tree : rest
        | Just close <- opening tree ->
            let (inside, afterInside) = go (Just close) rest
             in case afterInside of
                  closer : remaining
                    | leafToken closer == Just close ->
                        let (siblings, final) = go closing remaining
                         in (TreeNode BracketNode (tree : inside ++ [closer]) : siblings, final)
                  _ -> let (siblings, final) = go closing afterInside in (tree : inside ++ siblings, final)
        | Just token <- leafToken tree, Just token == closing -> ([], tree : rest)
        | Just token <- leafToken tree, token `elem` [TRParen, TRBracket, TRBrace], closing /= Nothing -> ([], tree : rest)
        | otherwise -> let (siblings, final) = go closing rest in (tree : siblings, final)
    opening tree = case leafToken tree of
      Just TLParen -> Just TRParen
      Just TLBracket -> Just TRBracket
      Just TLBrace -> Just TRBrace
      Just (TBraceKeyword _) -> Just TRBrace
      _ -> Nothing

leafToken :: Tree -> Maybe Token
leafToken = \case
  TreeLeaf Leaf {leafPiece = Just Piece {pieceKind = Lexeme token}} -> Just token
  _ -> Nothing

-- wrap each run of siblings that a mark covereth exactly, outermost first.
nest :: [(NodeKind, SourceSpan)] -> [Tree] -> [Tree]
nest [] trees = trees
nest marks trees = go marks trees
  where
    go _ [] = []
    go pending (tree : rest) = case treeSpan tree of
      Nothing -> tree : go pending rest
      Just SourceSpan {spanStart = start} ->
        let here = [mark | mark@(_, SourceSpan markStart _) <- pending, markStart == start]
            later = [mark | mark@(_, SourceSpan markStart _) <- pending, markStart > start]
         in case [(mark, covered, after) | mark@(_, SourceSpan _ end) <- here, Just (covered, after) <- [coverTo end (tree : rest)]] of
              ((kind, SourceSpan _ end), covered, after) : _ ->
                let inner = [mark | mark@(_, SourceSpan markStart markEnd) <- drop 1 here ++ later, markStart >= start, markEnd <= end, (mark /= (kind, SourceSpan start end))]
                    outer = [mark | mark@(_, SourceSpan markStart _) <- later, markStart >= end]
                 in TreeNode kind (nest inner covered) : go outer after
              [] -> descend (filter (within tree) later) tree : go (filter (not . within tree) later) rest
    descend inner = \case
      TreeNode kind children -> TreeNode kind (nest inner children)
      leaf -> leaf
    within tree (_, SourceSpan start end) = case treeSpan tree of
      Just SourceSpan {spanStart, spanEnd} -> start >= spanStart && end <= spanEnd
      Nothing -> False
    -- the siblings whose last token endeth exactly at the mark's end.
    coverTo end = walk []
      where
        walk taken = \case
          [] -> Nothing
          next : others -> case treeSpan next of
            Just SourceSpan {spanEnd}
              | spanEnd == end -> Just (reverse (next : taken), others)
              | spanEnd < end -> walk (next : taken) others
              | otherwise -> Nothing
            Nothing -> walk (next : taken) others
