# naming

audience: ai agents that name things in tung. purpose: how to choose a word
for a concept, and the words tung useth where they differ from the common
term. the rules hold for object-language names, keywords, host keys, `.tung`
paths, and library comments.

## choosing a word

- coin no new word: no compound, calque, or revived archaism made to avoid
  a common term.
- use an existing word with a germanic root when it naturally nameth the
  concept, as `next`, `leftover`, or `sift`.
- otherwise use the common word, whatever its root: `type`, `class`,
  `effect`, `function`, `axiom`, `proof`, `integer`, `map`.
- a word the table below doth not list taketh its common spelling. a listed
  word may yet be replaced by its common term; once replaced, do not bring
  the old word back.

a name useth the plain verb, as `gather`, `flip`, and `sift`, unless it
must tell the agent, the patient, or the event apart. an agent adjective,
describing the one who doeth, taketh `-and`; and an event
or an action taketh `-ing`, as `doing`. `-and` and `-ing` never stand for
each other. a patient is named by its past participle, as `sifted`.

## placeholder names

a value whose name carrieth no meaning taketh a letter from the start of the
alphabet: `a`, `b`, `c`, `d`, never `x`, `y`, `z`, `w`. this holdeth in code,
examples, documents, comments, and the names the checker invents when it
rendereth a type.

- a list is `a…`, `b…`; a matched value's fields are `a′`, `b′`.
- functions are `f`, `g`, `h`; types are greek, as `α`, `β`; a value never
  taketh a greek name. greek letters taken in order follow the old
  alphabet, with digamma and koppa: α β γ δ ε ϝ ζ η θ ι κ λ μ ν ξ ο π ϙ ρ σ
  τ υ φ χ ψ ω. a mnemonic letter may stand outside the order, as `ρ` for a
  ring or `ι` for an index.
- conventional letters keep their meaning: `n`, `m`, `k` for tales, `p`, `q`
  for proofs or quotients, and a field name such as `key` or `leftover`.
- a name with a meaning beateth a letter: `width`, `count`, `seen`.

## words that differ from the common term

| common term          | tung     | origin |
| -------------------- | -------- | ------ |
| absolute             | length   |        |
| absorb               | swallow  |        |
| age                  | eld      |        |
| cancel               | strike   |        |
| cardinality          | manyhood |        |
| change               | tweak    |        |
| commute              | swap     |        |
| condition            | kilter   |        |
| constant             | singal   |        |
| contain              | inhold   | calque |
| default              | fallback |        |
| double               | twofold  |        |
| eliminate            | unbuild  |        |
| example              | byspel   |        |
| exchange             | trade    |        |
| filter               | sift     |        |
| fixed                | fast     |        |
| fold                 | gather   |        |
| format               | tidy     |        |
| identity monad       | bare     |        |
| instance             | bizen    |        |
| is equal to          | is       |        |
| language             | tongue   |        |
| motive               | drive    |        |
| negate (number)      | flip     |        |
| negate (proposition) | gainsay  |        |
| number               | tale     |        |
| person               | wight    |        |
| remainder            | leftover |        |
| remove               | rid      |        |
| rest                 | leftover |        |
| result               | outcome  |        |
| second               | other    |        |
| separate             | shed     |        |
| single               | onefold  |        |
| singleton            | onesome  |        |
| state                | hade     |        |
| strict               | tight    |        |
| structure            | building |        |
| successor            | next     |        |
| universe             | world    |        |
