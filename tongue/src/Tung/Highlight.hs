-- | the source structure editors read, from one parse: token roles for
-- colouring, the tokens, declarations, and imports of the concrete tree, and
-- each local binder's scope, so no client relexeth or reparseth tung.
module Tung.Highlight
  ( SourceSyntax (..),
    DeclarationSummary (..),
    ImportSummary (..),
    highlightSource,
    sourceSyntaxSummary,
  )
where

import Data.Char (isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf)
import Data.Map.Strict qualified as Map
import Tung.Concrete (Leaf (..), NodeKind (..), Tree (..), treeSpan)
import Tung.Dependent.Source.Parse (SourceRole (..), sourceSyntax)
import Tung.Token

data SourceSyntax = SourceSyntax
  { syntaxRoles :: [(Int, Int, String, [String])],
    syntaxTokens :: [(Int, Int, String)],
    syntaxDeclarations :: [DeclarationSummary],
    syntaxImports :: [ImportSummary],
    -- each local binder and the span where it is seen.
    syntaxScopes :: [(Int, Int, Int, Int)]
  }

-- a `let`, `ilk`, `flock`, `bizen`, or `orsetting` from its keyword. the
-- header endeth where the body beginneth: after `≔`, or at the brace of an
-- ilk, flock, or bizen; a declaration without a body is all header.
data DeclarationSummary = DeclarationSummary
  { declarationKind :: String,
    declarationStart :: Int,
    declarationEnd :: Int,
    declarationHeaderEnd :: Int,
    declarationShown :: Bool,
    declarationDoc :: Maybe String
  }

data ImportSummary = ImportSummary
  { importPath :: String,
    importAlias :: Maybe String,
    importStart :: Int,
    importEnd :: Int
  }

-- roles by start, each range once.
highlightSource :: String -> [(Int, Int, String, [String])]
highlightSource = syntaxRoles . sourceSyntaxSummary

sourceSyntaxSummary :: String -> SourceSyntax
sourceSyntaxSummary source =
  SourceSyntax
    { syntaxRoles = [(start, end, role, modifiers) | (start, (end, role, modifiers)) <- Map.toAscList (Map.fromList [(spanStart span, (spanEnd span, role, modifiers)) | SourceRole span role modifiers <- roles])],
      syntaxTokens = [(spanStart pieceSpan, spanEnd pieceSpan, kind token) | Piece {pieceSpan, pieceKind = Lexeme token} <- leaves tree],
      syntaxDeclarations = [summary | TreeNode DeclarationNode children <- nodes, Just summary <- [declaration children]],
      syntaxImports = [summary | TreeNode DeclarationNode children <- nodes, Just summary <- [bring children]],
      syntaxScopes = [(spanStart binder, spanEnd binder, spanStart scope, spanEnd scope) | (binder, scope) <- scopes]
    }
  where
    (tree, roles, scopes) = sourceSyntax source
    nodes = universe tree
    kind = \case
      TIdent name | name `elem` keywordNames -> "keyword"
      TIdent _ -> "name"
      TText _ -> "string"
      TUnicode _ -> "character"
      TNatural _ -> "number"
      TInteger _ -> "number"
      TFloat _ -> "number"
      token | token `elem` [TLet, TFix, TExport, TImport, TType, TYield, TForeign, TClass, TInstance, TMatch, TSorry, TOrsend, TInduce, TFall] -> "keyword"
      _ -> "punctuation"

universe :: Tree -> [Tree]
universe tree =
  tree : case tree of
    TreeNode _ children -> concatMap universe children
    TreeLeaf _ -> []

leaves :: Tree -> [Piece]
leaves = \case
  TreeLeaf Leaf {leafPiece = Just piece} -> [piece]
  TreeLeaf _ -> []
  TreeNode _ children -> concatMap leaves children

tokenOf :: Piece -> Maybe Token
tokenOf Piece {pieceKind = Lexeme token} = Just token
tokenOf _ = Nothing

declaration :: [Tree] -> Maybe DeclarationSummary
declaration children = do
  let pieces = concatMap leaves children
  (shown, keyword) <- case pieces of
    first : second : _ | tokenOf first == Just TExport -> Just (True, second)
    first : _ -> Just (False, first)
    [] -> Nothing
  token <- tokenOf keyword
  SourceSpan _ end <- treeSpan (TreeNode DeclarationNode children)
  let headerEnd
        | token `elem` [TType, TClass, TInstance] = last (end : [spanStart (pieceSpan open) | TreeNode BracketNode (TreeLeaf Leaf {leafPiece = Just open} : _) <- children, tokenOf open == Just TLBrace])
        | otherwise = case dropWhile (not . isSign) children of
            _ : next : _ | Just (SourceSpan start _) <- treeSpan next -> start
            _ -> end
  if token `elem` [TLet, TFix, TType, TClass, TInstance, TOrsend]
    then Just (DeclarationSummary (pieceText keyword) (spanStart (pieceSpan keyword)) end headerEnd shown (documentation children))
    else Nothing
  where
    isSign = \case
      TreeLeaf Leaf {leafPiece = Just piece} -> tokenOf piece == Just TEquals
      _ -> False

-- the last doc comment before a declaration: `##` lines, or `/** … */`.
documentation :: [Tree] -> Maybe String
documentation children = case children of
  TreeLeaf Leaf {leafLeading} : _ -> case reverse (groups leafLeading) of
    group : _ | not (null (cleaned group)) -> Just (cleaned group)
    _ -> Nothing
  TreeNode _ inner : _ -> documentation inner
  [] -> Nothing
  where
    -- consecutive `##` lines form one group; a block doc is its own.
    groups = go []
      where
        go current = \case
          [] -> [reverse current | not (null current)]
          Piece {pieceKind = Comment _, pieceText} : rest
            | "##" `isPrefixOf` pieceText -> go (pieceText : current) rest
            | "/**" `isPrefixOf` pieceText -> [reverse current | not (null current)] ++ [[pieceText]] ++ go [] rest
          Piece {pieceKind = Space, pieceText} : rest | length (filter (== '\n') pieceText) <= 1 -> go current rest
          _ : rest -> [reverse current | not (null current)] ++ go [] rest
    cleaned = \case
      [block] | "/**" `isPrefixOf` block -> clean [dropWhile (`elem` " \t") (stripStar line) | line <- lines (dropEnd 2 (drop 3 block))]
      group -> clean [dropWhile (`elem` " \t") (drop 2 line) | line <- group]
    stripStar line = case dropWhile isSpace line of
      '*' : rest -> rest
      _ -> line
    dropEnd count = reverse . drop count . reverse
    clean = intercalate "\n" . dropWhileEnd null . dropWhile null . map trim
    trim = dropWhile isSpace . dropWhileEnd isSpace

bring :: [Tree] -> Maybe ImportSummary
bring children = case concatMap leaves children of
  keyword : rest | tokenOf keyword == Just TImport -> do
    let (path, alias) = segments rest
    first : _ <- Just path
    pure (ImportSummary (concatMap pieceText path) (pieceText <$> alias) (spanStart (pieceSpan first)) (spanEnd (pieceSpan (last path))))
  _ -> Nothing
  where
    segments = \case
      name : dot : more | isName name, tokenOf dot == Just TDot -> let (path, alias) = segments more in (name : dot : path, alias)
      [name, alias] | isName name, isName alias -> ([name], Just alias)
      name : _ | isName name -> ([name], Nothing)
      _ -> ([], Nothing)
    isName piece = case tokenOf piece of
      Just (TIdent _) -> True
      _ -> False
