module Test.Format (group) where

import Data.List (intercalate)
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung (formatSource)

group :: IO Group
group = Harness.group "format" (map formatCase cases ++ [idempotence, generatedIdempotence])

formatCase :: (String, String, String) -> Test
formatCase (name, source, expected) = expectEq name expected (formatSource source)

idempotence :: Test
idempotence = expect "formatter is idempotent" (all (\(_, source, _) -> isIdempotent source) cases)

generatedIdempotence :: Test
generatedIdempotence = expect "formatter is idempotent for generated structural sources" (all isIdempotent generatedSources)
  where
    generatedSources =
      [ intercalate "\n" (map (prefix ++) declaration) ++ ending
      | declaration <- declarations,
        prefix <- ["", " ", "  ", "\t"],
        ending <- ["", "\n"]
      ]
    declarations =
      [ ["show ilk box: [a:*, *] {", "box: [a, a box]", "}"],
        ["let result ≔", "match worth {", "yea; nay ^ 1", "}"],
        ["let handled ≔", "try risky {", "message fail ^ 0", "}"],
        ["flock sameness:[a:*, *] {", "let sameness:[@a:*, a, a]", "let rule:[@a:*, x:a,", "(x sameness) ≔ x]", "}"]
      ]

isIdempotent :: String -> Bool
isIdempotent source = formatSource formatted == formatted
  where
    formatted = formatSource source

cases :: [(String, String, String)]
cases =
  [ ( "consecutive case rows align their columns and arrows",
      """
      let drop ≔ {
        l, 0 ^ l,
        _, 0;
        empty, _ ^ empty,
        _ ‥ rest, n ^ rest drop (n - 1)
      }
      """,
      """
      let drop ≔ {
        l,        0 ^ l,
        _,        0;
        empty,    _ ^ empty,
        _ ‥ rest, n ^ rest drop (n - 1)
      }
      """
    ),
    ( "a body after a closed header continueth its declaration",
      """
      let kept: [
      x: ℕ,
      x = x
      ] ≔ {c: ℕ ^ c = c}
      transport eftbend eftbend
      let next ≔ 0
      """,
      """
      let kept: [
        x: ℕ,
        x = x
      ] ≔ {c: ℕ ^ c = c}
        transport eftbend eftbend
      let next ≔ 0
      """
    ),
    ( "a row body after its separator is indented",
      """
      let result ≔ match worth {
      yea ^
      1,
      nay ^ 0
      }
      """,
      """
      let result ≔ match worth {
        yea ^
          1,
        nay ^ 0
      }
      """
    ),
    ( "declaration annotations compact colons and indent the body once",
      """
      let sameness : [
      @α : *,
      x : α,
      α] ≔
      x
      let answer : ℤ ≔ +42

      """,
      """
      let sameness: [
        @α: *,
        x: α,
        α] ≔
        x
      let answer: ℤ ≔ +42

      """
    ),
    ( "braced bodies and composition use one indentation level",
      """
      show flock hath_+:[a:*, *] {
      let +:[a, a, a]
      }
      let paired:* ≔ >{
      pair,
      ℤ
      }

      """,
      """
      show flock hath_+: [a: *, *] {
        let +: [a, a, a]
      }
      let paired: * ≔ >{
        pair,
        ℤ
      }

      """
    ),
    ( "instance colon beginneth a declaration after a continued let",
      """
      let worth ≔
      +1
      bizen : ℤ ring {
      let -: [f:, g:] ≔ f
      }

      """,
      """
      let worth ≔
        +1
      bizen: ℤ ring {
        let -: [f:, g:] ≔ f
      }

      """
    ),
    ( "instance header brackets use one indentation level",
      """
      bizen:[@b:*, @:b ring,
      @a : *, [a, b] ring] {
      let -: [f:, g:, x:] ≔ (x f) - (x g)
      }

      """,
      """
      bizen: [@b: *, @: b ring,
        @a: *, [a, b] ring] {
        let -: [f:, g:, x:] ≔ (x f) - (x g)
      }

      """
    ),
    ( "a type colon hath one space after it",
      """
      let hath_+:[x : ℤ, y:  ℤ, ℤ] ≔ (x + y: ℤ)
      flock sameness:[a:*, *] { let rule:[x : a, x = x] }
      let record:r{field : ℤ} ≔ r{field: +1}
      let text ≔ 'x: y' # note: untouched
      let letter ≔ `:
      /* note: untouched */

      """,
      """
      let hath_+: [x: ℤ, y: ℤ, ℤ] ≔ (x + y: ℤ)
      flock sameness: [a: *, *] { let rule: [x: a, x = x] }
      let record: r{field: ℤ} ≔ r{field: +1}
      let text ≔ 'x: y' # note: untouched
      let letter ≔ `:
      /* note: untouched */

      """
    ),
    ( "sort use declarations",
      """
      use zebra.tung zebra
      use alpha.tung

      ## a separate use block.
      use delta.tung
      use beta.tung beta

      """,
      """
      use alpha.tung
      use zebra.tung zebra

      ## a separate use block.
      use beta.tung beta
      use delta.tung

      """
    ),
    ( "nested declarations",
      """
      show ilk box: [a:*, *] {
      box: [a, a box]
      }
      let text ≔ '{not a block}' # }

      """,
      """
      show ilk box: [a: *, *] {
        box: [a, a box]
      }
      let text ≔ '{not a block}' # }

      """
    ),
    ( "current application syntax",
      """
      show let sift:[x:a maybe, f:[a, 𝟚], a maybe] ≔ x match {
      a some ^ a f $ if (a some) none
      none   ^ none
      }

      """,
      """
      show let sift: [x: a maybe, f: [a, 𝟚], a maybe] ≔ x match {
        a some ^ a f $ if (a some) none
        none   ^ none
      }

      """
    ),
    ( "expression continuations",
      """
      let picked ≔
      match worth {
      yea ^ +1,
      nay ^ +0
      }
      let handled ≔
      try risky {
      yield worth ^ worth,
      message fail ^ +0
      }
      let sameness ≔
      { x ^ x }

      """,
      """
      let picked ≔
        match worth {
          yea ^ +1,
          nay ^ +0
        }
      let handled ≔
        try risky {
          yield worth ^ worth,
          message fail ^ +0
        }
      let sameness ≔
        { x ^ x }

      """
    ),
    ( "local result",
      """
      let main ≔ (
      let first ≔
      +1 + +2
      let second ≔ +3
      yield first + second
      )

      """,
      """
      let main ≔ (
        let first ≔
          +1 + +2
        let second ≔ +3
        yield first + second
      )

      """
    ),
    ( "nested continuation",
      """
      let fixtures ≔
      first ‥
      (second ‥
      (third ‥ empty))

      let next ≔
      worth

      """,
      """
      let fixtures ≔
        first ‥
          (second ‥
            (third ‥ empty))

      let next ≔
        worth

      """
    ),
    ( "split right side",
      """
      bizen:(float evenbraid) elementary {
      let sine: [a evenbraid b:] ≔
      (((0.0 offdraw_float b) evenbraid a) exponent)
      sine-from-exponents ((b evenbraid (0.0 offdraw_float a)) exponent)
      }

      """,
      """
      bizen: (float evenbraid) elementary {
        let sine: [a evenbraid b:] ≔
          (((0.0 offdraw_float b) evenbraid a) exponent)
            sine-from-exponents ((b evenbraid (0.0 offdraw_float a)) exponent)
      }

      """
    ),
    ( "body after a multiline header",
      """
      show let sameness:[worth:a, a] ≔
      worth

      """,
      """
      show let sameness: [worth: a, a] ≔
        worth

      """
    ),
    ( "multiline bracket header keepeth one indentation level",
      """
      show let lift₃:[
      a₀:a₀ f,
      a₁:a₁ f,
      a₂:a₂ f,
      f:[a₀, a₁, a₂, b],
      b f] ≔
      >{atfold, a₂, a₁, a₀, f sheer}

      """,
      """
      show let lift₃: [
        a₀: a₀ f,
        a₁: a₁ f,
        a₂: a₂ f,
        f: [a₀, a₁, a₂, b],
        b f] ≔
        >{atfold, a₂, a₁, a₀, f sheer}

      """
    ),
    ( "multiline record",
      """
      let person:r{
      name:text,
      age:ℤ
      } ≔ r{
      name ≔ 'naoki',
      age ≔ +35
      }

      """,
      """
      let person: r{
        name: text,
        age: ℤ
      } ≔ r{
        name ≔ 'naoki',
        age ≔ +35
      }

      """
    ),
    ( "associative sequence",
      """
      let list ≔ >{
      ‥,
      a,
      b,
      empty
      }

      """,
      """
      let list ≔ >{
        ‥,
        a,
        b,
        empty
      }

      """
    ),
    ( "multiline law annotation",
      """
      flock atfoldsome:[f:[*, *], *] {
      let rule:[a:a f,
      (a atfold (sameness sheer)) = a]
      let sheer_rule:[a:a, (a sheer) = (a sheer)]
      }

      """,
      """
      flock atfoldsome: [f: [*, *], *] {
        let rule: [a: a f,
          (a atfold (sameness sheer)) = a]
        let sheer_rule: [a: a, (a sheer) = (a sheer)]
      }

      """
    ),
    ( "equals signs in strings and comments",
      """
      let text ≔ 'a = b' # =
      let next ≔ +1

      """,
      """
      let text ≔ 'a = b' # =
      let next ≔ +1

      """
    ),
    ( "decimal unicode and block comments",
      """
      let result ≔
      match character {
      `\\32; ^ 1,
      _ ^ 0
      }
      /*
        {
      */
      let next ≔ 1

      """,
      """
      let result ≔
        match character {
          `\\32; ^ 1,
          _     ^ 0
        }
      /*
        {
      */
      let next ≔ 1

      """
    ),
    ( "delimiters in block comments",
      """
      let x ≔ +1 /* { = */
      let y ≔ +2
      /*
        {
      */
      let z ≔ +3

      """,
      """
      let x ≔ +1 /* { = */
      let y ≔ +2
      /*
        {
      */
      let z ≔ +3

      """
    ),
    ( "windows newlines",
      "ilk box: * {\r\nbox: box\r\n}\r\n",
      """
      ilk box: * {
        box: box
      }

      """
    ),
    ( "blank line endeth continuation",
      """
      show let worth ≔
        +1

      ## the next declaration.
      show let next ≔ +2

      """,
      """
      show let worth ≔
        +1

      ## the next declaration.
      show let next ≔ +2

      """
    ),
    ( "comment useth structural indentation",
      """
      flock sameness: [a: *, *] {
        let rule: [x: a,
        # the equation.
          (x sameness) = x]
        # the next law.
        let next_rule: [x: a, (x sameness) = x]
      }

      """,
      """
      flock sameness: [a: *, *] {
        let rule: [x: a,
        # the equation.
          (x sameness) = x]
        # the next law.
        let next_rule: [x: a, (x sameness) = x]
      }

      """
    )
  ]
