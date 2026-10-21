module Test.Format (group) where

import Data.Char (isSpace)
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung (formatSource)

group :: IO Group
group = Harness.group "format" (map neatenCase cases ++ [refusal, idempotence, canonical])

neatenCase :: (String, String, String) -> Test
neatenCase (name, source, expected) = expectEq name (Right expected) (formatSource source)

refusal :: Test
refusal = expectEq "source that doth not parse is refused" (Left "expected an expression") (formatSource "let worth ≔ (\n")

idempotence :: Test
idempotence = expect "neatening is idempotent" (all (\(_, source, _) -> formatSource source == (formatSource source >>= formatSource)) cases)

-- the neat form followeth the tokens alone: breaking every space into a
-- line, or joining every line into one, changeth nothing while each
-- comment keepeth its place before or after a line end.
canonical :: Test
canonical = expect "whitespace never changeth the neat form" (all same cases)
  where
    same (_, source, _) = all (\respaced -> formatSource respaced == formatSource source) [respace True source, respace False source]

respace :: Bool -> String -> String
respace split = go False
  where
    go _ [] = []
    go _ ('\'' : rest) = let (text, remaining) = quoted rest in '\'' : text ++ go False remaining
    go _ ('#' : rest) = let (comment, remaining) = break (== '\n') rest in '#' : comment ++ '\n' : go True (drop 1 remaining)
    go _ ('/' : '*' : rest) = let (comment, remaining) = block rest in "/*" ++ comment ++ go False remaining
    go afterComment text@(character : _)
      | isSpace character =
          let (blank, remaining) = span isSpace text
              beforeComment = take 1 remaining == "#" || take 2 remaining == "/*"
              broken = '\n' `elem` blank
           in (if beforeComment then (if broken then "\n" else " ") else if split then "\n  " else if afterComment then "" else " ") ++ go False remaining
    go _ (character : rest) = character : go False rest
    block = \case
      '*' : '/' : rest -> ("*/", rest)
      character : rest -> let (comment, remaining) = block rest in (character : comment, remaining)
      [] -> ([], [])
    quoted = \case
      '\\' : character : rest -> let (text, remaining) = quoted rest in ('\\' : character : text, remaining)
      '\'' : rest -> ("'", rest)
      character : rest -> let (text, remaining) = quoted rest in (character : text, remaining)
      [] -> ([], [])

cases :: [(String, String, String)]
cases =
  [ ( "redundant parentheses are dropped where the parse cannot change",
      "let a ≔ (m warp)\nlet b ≔ g ((x)) (h) f(x)y [(q r), (c)]\nlet c ≔ g (m tweak) @([α, β]) @({a ^ a}) @(α) @(ℕ list) (p).left (x: ℕ) ((a b) c)\nlet d ≔ ({a ^ (a f)})\nlet e ≔ (a /* kept */ b)\nyield (a b)\n",
      """
      let a ≔ m warp

      let b ≔ g x h f x y [q r, c]

      let c ≔ g (m tweak) @[α, β] @{a ^ a} @α @(ℕ list) (p).left (x: ℕ) ((a b) c)

      let d ≔ f

      let e ≔ (a /* kept */
        b)

      yield a b

      """
    ),
    ( "a redundant η-expansion is shortened, to a parenthesised partial application when arguments remain; rows, annotations, and comments keep theirs",
      "let a ≔ g {x, y ^ x f y} {x ^ x {y ^ y h}}\nlet t ≔ g {b ^ m tweak b} ({b ^ m tweak b}) {b ^ b tweak m}\nlet b ≔ match q { x ^ x f, y ^ {x ^ x f} }\nlet c ≔ {x: ℕ ^ x f} {@x ^ x f} {x ^ x x} {x, x ^ x f x}\nlet d ≔ {x ^ /* kept */ x f}\n",
      """
      let a ≔ g f h

      let t ≔ g (m tweak) (m tweak) {b ^ b tweak m}

      let b ≔ match q {
        x ^ x f,
        y ^ f
      }

      let c ≔ {x: ℕ ^ x f} {@x ^ x f} {x ^ x x} {x, x ^ x f x}

      let d ≔ {x ^ /* kept */
        x f}

      """
    ),
    ( "spacing is fixed and brings are sorted together",
      "bring ilk/two.tung\n\n\nbring ilk/list.tung\nlet   a:ℕ≔1\nlet b\n  :ℕ ≔\n   2\n",
      """
      bring ilk/list.tung
      bring ilk/two.tung

      let a: ℕ ≔ 1

      let b: ℕ ≔ 2

      """
    ),
    ( "comments keep their tokens and case blocks of several rows break",
      "## doc for f.\nlet f: [𝟚, ℕ] ≔ { yea ^ 1, nay ^ 0 } # trailing\n# before g\nlet g: [x: ℕ, ℕ] ≔ match x { 0 ^ 0, k heir ^ k }\n",
      """
      ## doc for f.
      let f: [𝟚, ℕ] ≔ {
        yea ^ 1,
        nay ^ 0
      } # trailing

      # before g
      let g: [x: ℕ, ℕ] ≔ match x {
        0      ^ 0,
        k heir ^ k
      }

      """
    ),
    ( "a wide binding putteth its body, and its annotation when wide, on lines of their own",
      "let exchange: [a: ℕ, b: ℕ, c: ℕ, d: ℕ, ((a + b) + (c + d)) = ((a + c) + (b + d))] ≔ sorry\nlet total: ℕ ≔ first_long_name + second_long_name + third_long_name + fourth_name\nlet chain: [a = d] ≔ >{throughgo, first_long_proof_step, second_long_proof_step, third_long_proof_step}\n",
      """
      let exchange
        : [a: ℕ, b: ℕ, c: ℕ, d: ℕ, ((a + b) + (c + d)) = ((a + c) + (b + d))]
        ≔ sorry

      let total: ℕ
        ≔ first_long_name + second_long_name + third_long_name + fourth_name

      let chain: [a = d] ≔ >{throughgo,
        first_long_proof_step,
        second_long_proof_step,
        third_long_proof_step
      }

      """
    ),
    ( "wide comments wrap; quoted text and block comments stay whole",
      "## a comment that runneth past the limit is broken at the last space that fitteth within it.\nlet greeting: string ≔ 'a long quoted greeting that must never be broken across two lines and more'\n/* a block\n   comment */\nlet after ≔ 1\n",
      """
      ## a comment that runneth past the limit is broken at the last space that
      ## fitteth within it.
      let greeting: string
        ≔ 'a long quoted greeting that must never be broken across two lines and more'

      /* a block
         comment */
      let after ≔ 1

      """
    ),
    ( "a flock body breaketh with a blank line between members and a short lambda stayeth whole",
      "flock hath_flip: [α: *, *] { let flip: [α, α] let flip_flip: [x: α, (x flip $ flip) = x] }\nlet twice: [ℕ, ℕ] ≔ {x ^ (x + x)}\n",
      """
      flock hath_flip: [α: *, *] {
        let flip: [α, α]

        let flip_flip: [x: α, (x flip $ flip) = x]
      }

      let twice: [ℕ, ℕ] ≔ {x ^ x + x}

      """
    ),
    ( "a bizen body breaketh with a blank line between members",
      "bizen: ℕ hath_flip { let flip ≔ heir let flip_flip ≔ sorry }\n",
      """
      bizen: ℕ hath_flip {
        let flip ≔ heir

        let flip_flip ≔ sorry
      }

      """
    ),
    ( "a wide block breaketh while its binding keepeth one line",
      "let kept ≔ (let a ≔ 1 yield a)\nlet wide ≔ (let first_long_name ≔ 1 let second_long_name ≔ 2 let third_long_name ≔ 3 yield first_long_name)\n",
      """
      let kept ≔ (let a ≔ 1 yield a)

      let wide ≔ (
        let first_long_name ≔ 1
        let second_long_name ≔ 2
        let third_long_name ≔ 3
        yield first_long_name
      )

      """
    )
  ]
