# tung language reference

audience: agents. purpose: what a program author writeth and observeth:
syntax, names, libraries, the runner, and command-line output.
[`dependent.md`](dependent.md) owneth checking algorithms and the logical
boundary; [`development.md`](development.md) owneth implementation and
commands. [`byspel/walkthrough.tung`](../byspel/walkthrough.tung) is the
checked introduction.

## keywords

| keyword | meaning                         | keyword    | meaning                       |
| ------- | ------------------------------- | ---------- | ----------------------------- |
| `let`   | declaration                     | `match`    | pattern match                 |
| `fast`  | self-calling effect declaration | `unbuild`  | eliminator of a type or class |
| `show`  | export                          | `function` | annotated function expression |
| `bring` | import                          | `sorry`    | unfinished assumption         |
| `yield` | result of a local block         | `axiom`    | named axiom                   |
| `type`  | inductive family (data type)    | `foreign`  | foreign host binding          |
| `class` | type class                      | `effect`   | primitive action type (io)    |
| `bizen` | instance                        |            |                               |

`fallback`, in `bizen fallback:`, marketh a default instance, and `out`, in
`β: * out`, an output parameter; both are ordinary names elsewhere.

## files and modules

a `.tung` file containeth declarations, private unless shown:

- `show let …`, `show type …`, and `show class …` export declarations;
  `show type` also exporteth its constructors and eliminator.
- `show name` re-exporteth a visible name; `show ns~name` exporteth it as
  `name`. a plain `bring` re-exporteth nothing.

lets, types, constructors, classes, and members share one namespace, and a
module declareth each top-level name once. declared names are unqualified.
the library useth `_request` beside constructor `request`, and `hath_zero`
beside member `zero`, to avoid collisions.

### libraries and imports

`bring path.tung alias` importeth a module. without the optional alias, the
namespace is the last path segment before its first dot.

```tung
bring type/list.tung
bring type/table.tung hashmap

let xs ≔ list~empty
let entries ≔ hashmap~empty
```

- an imported name may stay bare while unambiguous; otherwise qualify it.
- two direct imports cannot claim one namespace. imports must be acyclic.
- local names shadow imported bare names, including constructors in patterns;
  qualification still reacheth the import.
- re-exports keep their defining identities. shared dependencies must agree on
  them; one dependency reached along several paths is fine.
- missing, conflicting, and cyclic imports are reported at the owning `bring`.

lookup searcheth relative to the importing file, then declared library roots,
then `TUNG_PATH`. one import path resolving to different files is ambiguous.
`often.tung` is an optional import; there is no automatic prelude.

### manifests

`tung.yaml` declareth local libraries or pinned git repositories:

```yaml
dependencies:
  library:
    path: library
  example:
    repo: https://example.org/example.git
    hash: "0123456789012345678901234567890123456789"
    subdir: library
```

- `path` is a live directory, absolute or relative to its manifest.
- `repo` is a git URL or local repository path and requireth `hash`, a full,
  quoted, 40- or 64-digit hexadecimal commit. a dependency hath either `path`
  or `repo` with `hash`.
- optional `subdir` selecteth a directory within the pinned checkout; it may
  not contain `..` or escape the checkout through symlinks.
- `bring` paths are relative to the selected library root.
- an optional `proof` field holdeth the [axiom policy](#proof-checking).

tung findeth the nearest manifest above the source file; each dependency may
have its own. git checkouts live in `.tung/libraries/` beside the root
manifest and work offline after their first fetch.
`tung --library-paths [project-path]` listeth the resolved roots.

resolution checketh the whole graph, including unused libraries. matching pins
or local paths share one root. these conflict, and the root cannot override
them:

- one dependency name with different sources or commits;
- one repository locator and subdirectory with different names or commits;
- one canonical local path with different names.

different subdirectories may name different libraries. local paths are
canonicalised, relative git paths lexically normalised, and remote locators
compared as written. `TUNG_PATH` is outside conflict checking, but duplicate
import paths stay ambiguous.

the standard library is an ordinary library in [`library/`](../library/). an external
project may pin `https://github.com/svartaz/tung.git` at a published hash with
`subdir: library`.

## names, comments, and literals

most non-space, non-reserved characters may occur in names. punctuation:

| spelling | meaning                             |
| -------- | ----------------------------------- |
| `~`      | imported namespace, as `list~empty` |
| `.`      | field projection, as `wight.name`   |
| `^`      | patterns followed by their result   |
| `≔`      | definition                          |
| `*`      | universe, only when standalone      |
| `_`      | discarded input or pattern          |

outside import paths, a name hath at most one `~`, with nonempty, slash-free
parts. `‥`, `·`, `→`, and `=` are ordinary names; there is no general infix
escape. names are snake_case, including host keys and paths; `-` remaineth
legal. generic polymorphic parameters use Greek letters.
[`naming.md`](../naming.md) owneth word choice.

`#` starteth a line comment; `/* … */` is a non-nested block comment. `##` and
`/** … */` document the next declaration.

| literal                  | type      | example           |
| ------------------------ | --------- | ----------------- |
| unsigned integer         | `ℕ`       | `42`              |
| signed integer           | `ℤ`       | `+42`, `-7`, `+0` |
| decimal                  | `float`   | `0.5`, `-2.0`     |
| backtick character       | `unicode` | `` `a ``          |
| single-quoted characters | `string`  | `'hello'`         |

`ℕ` and `ℤ` have arbitrary precision. `+ 1` applieth the name `+` to natural
`1`. natural subtraction stoppeth at zero. characters and strings accept
`\n`, `\r`, `\t`, `\'`, `\\`, and decimal escapes such as `\23383;`. a
character is one unicode scalar.

## application

functions are curried. in an unmarked sequence the second term is the
function and the others are its arguments in order:

```tung
a f           # f a
a f b c       # f a b c
a f $ g b     # g (f a) b
```

`$` groupeth its left side and putteth the next function first; `$(…)`
delimiteth such a segment. for values and types alike:

- `<{f, a, b, c}` meaneth `(a f b) f c`, and `>{f, a, b, c}` meaneth
  `a f (b f c)`. each needeth a function and at least two operands, and the
  marker toucheth `{`.
- `_` as an explicit input maketh its innermost application a function of
  each `_`, left to right: `_ ‥ k` is `{a ^ a ‥ k}`, and `_ + _` is
  `{a, b ^ a + b}`. a nested application is a function of its own holes, so
  `+1 ‥ (+2 ‥ _)` giveth the outer `‥` a function. a lone `_` is no term; in
  patterns and binders `_` still discardeth an input.

evaluation is call-by-need: inputs, lets, globals, and constructor fields are
shared and computed when inspected. `match` computeth only its selected branch,
and unused `sorry` doth not fail. pure native operations compute their inputs
fully; [effects](#effects) compute host inputs and results fully.

## declarations and types

types and values share one expression syntax. `*` is a universe with an
inferred level; universes are predicative and levels are never written.
`[*, *]` is a function from types to types. transparent definitions unfold
when types are compared.

### let declarations

```tung
let count ≔ 42
let answer: ℤ ≔ +42
let identity: [@α: *, a: α, α] ≔ a
let call: [@α: *, @β: *, f: [α, β], a: α, β] ≔ a f
let add_after: [a:, b: ℤ, ℤ] ≔ a + b
```

`let name ≔ body` inferreth a type; `let name: annotation ≔ body` checketh
against one. the header is one name; inputs belong in the annotation:

- a bare type annotateth a value. a bracket listeth inputs, then a final bare
  result type; a bracket of one bare expression is that expression.
- `name: type` bindeth an input and `name:` inferreth its type from use.
  `pattern: type` destructureth it ([patterns](#patterns)); `_: type`
  discardeth it. `_` is never a type.
- bare input types bind no names; the body supplieth their function.
- named and implicit slots precede bare slots. after a named last slot the
  result may be omitted for inference.
- the tidier writeth `a: α`: no space before `:`, one after.

a let's type must be determined: unknown types are never implicitly
quantified, so write polymorphic parameters. every name in an annotation is
already in scope or bound earlier in it.

`function inputs, result ^ body` is a function expression with its own
annotation, needing at least one input and a result. a let returning `*` is an
ordinary transparent type function; it may take value inputs or requirements
and be partially applied:

```tung
let identity ≔ function @α: *, a: α, α ^ a
let powerset: [α: *, *] ≔ [α, 𝟚]
let integer_type: * ≔ ℤ
```

`(term: type)` ascribeth any expression. `α ∧ β` is the product type and
`a ⸴ b` a product value. `→`, from `combinator.tung` and re-exported by
`often.tung`, is `show let →: [α: *, β: *, *] ≔ [α, β]`. it hath no special
associativity, so write `α → (β → γ)`, and may be passed unapplied, as in
`bizen: → semigroupoid`.

### implicit arguments and polymorphism

`@name: type` bindeth an implicit input; `@: type` requireth unnamed evidence.
type parameters are `@α: *`, a unary type constructor `@φ: [*, *]`; they may
also range over values.

calls may supply implicit inputs: written `@` arguments fill implicit
parameters in declaration order, even after value arguments, and a function
without one rejecteth `@`. omitted inputs are inferred or found by
[instance search](#classes-bizens-and-laws). a supplied input must have its
declared type, even when unused.

```tung
let f: [@α: *, @β: *, a: α, _: β, α] ≔ a
'x' f empty
'x' f @string empty
'x' f @string @(string list) empty
```

type inputs are erased before evaluation; implicit value inputs stay runtime
arguments. declared parameters are in scope in the body and may be forwarded
as `@α`.

quantifiers may occur at any rank; higher rank needeth annotations:

```tung
type pair: * { pair_of: [ℤ, string, pair] }
let both: [f: [@α: *, α, α], pair] ≔ (+1 f) pair_of ('x' f)
let make: [_: ℤ, [@α: *, α, α]] ≔ {a ^ a}
```

`both` requireth one function for every `α`, instantiated at each call;
`make` returneth such a function. nested quantifiers scope over their bracket
and may shadow outer variables.

### local blocks and recursion

a local block holdeth declarations and endeth with `yield`:

```tung
let seven ≔ (
  let six ≔ +2 · +3
  yield six + +1
)
```

imports, exports, types, axioms, foreign bindings, and fast declarations
are top-level only.

a let whose body nameth itself is recursive and needeth an annotation,
possibly on its body. its name shadoweth imports in that body, where
qualification still reacheth them, but an outer local of that name keepeth
precedence. recursion descendeth structurally: a
call supplieth a checked descendant, fixed explicit inputs, and explicit
indices, and may leave trailing other inputs unapplied. the bare recursive
name cannot be passed on, and mutually recursive lets are rejected.
[pattern matching and recursion](dependent.md#pattern-matching-and-recursion)
stateth the indexed, mutual, nested-container, and function-field rules.

`fast name: annotation ≔ body` declareth a fixed point. its header is a let
header, and `show fast` exporteth it. its body may name it anywhere, called,
partly applied, or passed on, with no structural check:

```tung
fast gather: [seen: string list, (string list) effect] ≔ read bind {
  none      ^ seen pure,
  line some ^ (line ‥ seen) gather
}
```

a fast declaration is rejected when:

- it hath no annotation;
- its type, after normalisation and its inputs, endeth in anything but an effect,
  as `nat`, `[nat, nat]`, or a type wrapping an effect. only effects may run
  without bound;
- its body never nameth it; that is a let;
- it bindeth `foreign`, is a bizen member, or standeth in a local block.

there are no mutual fast declarations. checking never unfoldeth one, so
nothing is proved by its body; [effects](#effects) stateth how one runneth.

well-founded recursion is library code in `type/accessible.tung`:
`wellfounded_recur_by` taketh a result motive, a measure, a
well-foundedness proof, a step, and an input, and the step's recursive call
requireth a smaller-measure proof. `type/natural.tung` provideth
`under_wellfounded` and `type/list_theorem.tung` `‥_manyhood_under` for list
tails; [`wellfounded.tung`](../byspel/wellfounded.tung) is an example.

## types

`type name: signature { constructors }` declareth a family whose signature
endeth in `*`. constructors are comma-separated and state full result types:

```tung
type list: [α: *, *] {
  empty: α list,
  ‥: [α, α list, α list]
}
```

- constructors are curried and return the family at full arity. header
  parameters scope over them.
- a constructor may add leading implicit parameters, which cannot redeclare
  owner parameters; when matched they are existential and cannot escape.
- constructors may select result indices, and matching refineth them in that
  branch:

```tung
type tag: [α: *, *] {
  integer: [ℤ, ℤ tag],
  textual: [string, string tag]
}
let unpack: [@α: *, a: α tag, α] ≔ match a {
  n integer ^ n,
  s textual ^ s
}
```

mutually dependent types form one group: uniform parameters agree in type and
visibility, result universes agree, and indices may differ. signatures cannot
depend on group members. negative occurrences and cycles through non-type
declarations are rejected.

one list family holdeth values, types, or type constructors;
[ordinary lists](dependent.md#ordinary-lists) hath checked examples.

### patterns

`match a, b { rows }` examineth values; `{ rows }` is a curried pattern
function. each row hath one pattern per input:

```tung
let not: [𝟚, 𝟚] ≔ {yea ^ nay, nay ^ yea}
let chosen ≔ match yea, nay {
  yea, b; b, yea ^ b,
  nay, _ ^ nay
}
let classify: [string, ℤ] ≔ {'yes' ^ +1, _ ^ +0}
```

- `^` separateth patterns from the result; `;` joineth complete alternative
  rows that share one result.
- a variable bindeth once per row; `_` discardeth.
- constructors follow second-is-function order, as `a ‥ leftover`.
- natural, integer, and string literals match exactly; integer and string
  literal rows need a catch-all. `0` and `n next` cover the naturals.
- rows must be exhaustive and non-redundant; impossible constructors need no
  row. `{}` eliminateth an annotated uninhabited input.
- a case function that destructureth constructors needeth an expected type.

a named annotation slot may hold a constructor pattern without parentheses,
`[a ⸴ b: α ∧ β, α]`; literal patterns belong in `match`. matching
`reflect: a = b` refineth the result, while `_: a = b` discardeth the proof.

`n next` matcheth a positive natural and bindeth its predecessor; as a term,
`next` addeth one unless a constructor of that name is in scope.
`n nonnegative` and `n next_negative` cover nonnegative and negative
integers; `3 next_negative` is `-4`.

matching a computed scrutinee replaceth its occurrences in the expected result
with the branch constructor. an indexed constructor may determine fields: a
tail of `α vec 2` hath index `1`. index patterns must be linear constructor
shapes; stuck computed indices are rejected. the
[dependent rules](dependent.md#pattern-matching-and-recursion) state the
precise restrictions.

`inspect` from `is.tung` also passeth the branch equation:
`e inspect {p, known ^ body, …}` giveth `known: e = p`, matching a fresh input
rather than refining `e`. when its result family cannot be inferred, write
`e inspect @τ @{_ ^ T} {p, known ^ body, …}`.

### induction

`unbuild name` is the eliminator of a type or class; `name` may be qualified,
and other names are rejected. a single-family eliminator taketh implicit
parameters, a motive, one method per constructor, indices, and the value:

```tung
let doubled: [l: ℕ list, ℕ list] ≔
  {_: ℕ list ^ ℕ list} unbuild list empty {a, _, leftover ^ a ‥ (a ‥ leftover)} l
```

mutual induction taketh one motive per family, then methods in family and
constructor order; nested recursive containers add their own motives and
methods. [inductive declarations](dependent.md#inductive-declarations-and-proofs)
defineth the method signatures.

### fields

an unindexed type with one constructor hath a field per named explicit
constructor input. `value.field` projecteth it; chains read leftward.

```tung
type wight: * { wight_of: [name: string, eld: ℤ, wight] }
let someone: wight ≔ 'naoki' wight_of +35
let older ≔ someone.name wight_of (someone.eld + +1)
```

separate types may share field names. nested constructor brackets extend the
fields; a later repeated name shadoweth an earlier one. indexed and
multi-constructor types have no fields. there is no anonymous record or update
syntax.

## classes, bizens, and laws

`class` declareth a type class and `bizen` an instance. headers end in `*`,
with named parameters and optional `@: parent` requirements:

```tung
class hath_≍: [α: *, *] {
  let ≍: [α, α, 𝟚]
  let ≍_reflect: [a: α, (a ≍ a) = yea]
}

bizen: 𝟚 hath_≍ {
  let ≍ ≔ {yea, yea ^ yea, nay, nay ^ yea, _, _ ^ nay}
  let ≍_reflect ≔ {yea ^ reflect, nay ^ reflect}
}
```

- class parameters omit `@`; members may add their own implicit parameters.
- `@: α hath_≍` requireth a dictionary. requirements may interleave with
  implicit parameters but name only preceding ones.
- a member is `let name: type` without a body. a law is a member whose type
  requireth a proof; it hath no separate syntax, is no rewrite rule, and is
  never evaluated when unused. laws concern the methods actually supplied.
- a bizen head is a class application in second-is-function order, after its
  parameters and requirements in one bracket:
  `bizen: [@α: *, @: α hath_≍, (α list) hath_≍] { … }`. bizen parameters are
  implicit.
- bizen members are lets, each required name once; missing, unknown, and
  repeated members, and duplicate instances, are rejected. annotations must
  agree with the class, and members are checked in class order.
- later members may use earlier ones; a member's own body referreth to its
  global accessor, so recursive methods need ordinary recursive helpers.
- an available parent dictionary taketh precedence; otherwise supplied parent
  members construct the parent inline.

search trieth local dictionaries, then registered bizens, then inherited
instances. registered bizens go by descending priority, then newest first, and
the first success is chosen. `bizen 10: …` setteth a priority (default 1000).
duplicate instance types are rejected. `β: * out` marketh an output parameter
for search to determine; unknown input heads postpone search. a
`bizen fallback: …` may resolve an otherwise stuck goal, and a goal still
unsolved needeth an annotation.
[classes and bizens](dependent.md#classes-and-bizens) stateth cycles, candidate
requirements, and depth limits.

## equality and assumptions

`is.tung`, re-exported by `often.tung`, defineth the ordinary indexed identity
type `=` with sole constructor `reflect`, which proveth an equation that
holdeth by computation. matching it rewriteth one endpoint to the other;
matching equal constructors equateth their fields, and different constructors
make the branch impossible. `≍` is boolean equality; `≔` defineth a name.

```tung
bring is.tung
let one: ℕ ≔ 1
let checked: one = 1 ≔ reflect
let symmetry: [@α: *, @a: α, @b: α, p: a = b, b = a] ≔
  match p {reflect ^ reflect}
```

`is.tung` also provideth `leibnitz`, `symmetry`, `transit`, `transport`,
`inspect`, function extensionality as the axiom `extend`, the type negation
`α ¬`, which is `[α, 𝟘]`, and `a ≠ b`, which is `(a = b) ¬`.

computation includeth η. a function equaleth the lambda that applieth it, and a
value of a type with one constructor, no indices, and no field of its own type
equaleth that constructor applied to its fields, so a match on an unknown
pair computeth and every `𝟙` is `only`:

```tung
let swap: [@α: *, @β: *, α ∧ β, β ∧ α] ≔ {a ⸴ b ^ b ⸴ a}
let swap_swap: [@α: *, @β: *, p: α ∧ β, ((p swap) swap) = p] ≔ reflect
```

- `sorry` inhabiteth any expected type as an unfinished assumption. inspecting
  it faileth at runtime; leaving it unused doth nothing.
- `axiom name: type` declareth a named axiom without a body. its
  annotation bindeth no inputs; it may be shown. reaching it at runtime faileth
  with `reached axiom 'name'`.
- checking accepteth both; [`--name`](#proof-checking) auditeth them. the
  [logical boundary](dependent.md#logical-boundary) stateth what this entaileth.

## effects

`α effect` is a runner action returning `α`, like haskell `IO` or purescript
`Effect`. evaluating, storing, passing, and combining effects performeth nothing.
a performed effect's host inputs and results are computed fully, including
constructor fields; contained functions and effects stay unperformed.

`effect.tung` provideth the monad operations:

- `pure` wrappeth a value; `map` changeth the result; `bind` chooseth the
  next effect from it; `then` performeth two and keepeth the latter result, and
  `>{then, a, b, c}` performeth several in order.
- `lift₂`, `apply`, and `each` perform effects left to right.
- a [fast declaration](#local-blocks-and-recursion) loopeth without bound;
  bounded repetition useth induction. calling a fast function buildeth an effect
  and performeth nothing. performing it evaluateth its inputs to their outer
  form and then unfoldeth its body, so a loop's accumulator holdeth no chain of
  pending computations, and a self-call outside any bind loopeth only when
  performed.

```tung
let main: 𝟙 effect ≔ read bind {
  line some ^ line write_line,
  none ^ 'no input' write_line
}
```

fallible operations return values: `optional` for absence, or `ε ∨ α` with
`inject₀` for failure and `inject₁` for success. file and process operations
use `string ∨ α`; `read` returneth none at end of input. library wrappers keep
this sequencing:

- `effect/fallible.tung`: `ε fallible α` wrappeth `(ε ∨ α) effect`;
  `fail` faileth, `handle` handleth a fault, and `bind` stoppeth at it.
- `type/hade.tung`: `σ hade φ α` wrappeth `[σ, (α ∧ σ) φ]` for any monad `φ`;
  `get`, `put`, and `tweak` read and change the state. `σ hade effect α` may
  perform effects, and `σ hade bare α`, with `bare` from `type/bare.tung`, is
  pure.
- both provide `lift` and `unwrap`, which giveth the step beneath; qualify
  them when both are imported.

tasks are opaque: `fork`, `wait`, `wait_for`, and `strike` control them.

## host bindings

an annotated top-level let may bind a foreign operation:

```tung
let write: [string, 𝟙 effect] ≔ 'write' foreign
let add_natural: [ℕ, ℕ, ℕ] ≔ 'add_natural' foreign {
  m, 0      ^ m,
  m, k next ^ (m add_natural k) next
}
```

- the string key and complete type must match the host catalogue. a binding
  without arguments needeth an effect type.
- a pure operation may give a checked structural model after `foreign`; effect
  operations cannot, and named annotation inputs require one. literal inputs
  compute natively during checking and other inputs unfold the model; the
  runner always useth the native operation.
- `ℕ`, `ℤ`, `float`, `unicode`, and `string` are primitive types whose
  operations and bizens come from library imports, usually `often.tung`.
  `effect` and `task` are opaque primitive families of kind `[*, *]` without
  constructors or eliminators.
- host data families such as `list`, `optional`, `table`, and `𝟙` are the
  types declared at their library paths; a same-spelled type elsewhere is a
  different type.

[host binding rules](dependent.md#effects-and-host-bindings) state the required
schemas; the [library guide](../library/reference.md) owneth library
contracts.

## command line

### running

a runnable file declareth a local `main: 𝟙 effect`; functions and other result
types are rejected. the runner performeth it once, leaving unused definitions
alone, and printeth nothing beyond the program's output. parse, type, and
runtime errors print diagnostics and return status 1. trailing command
arguments reach `arguments`. `exit` endeth the run, or only its task inside
one. a final interactive `yield` performeth an effect or fully computeth a value
before printing it.

### checking

`--check` and `--check-stdin` check a module or a program: a file without
`main` is a module, and a declared `main` must be runnable as above. status is
0 on success and 1 on rejection. output includeth:

- `type ok` after success;
- `sorry: name` for each shown declaration, bizen, or `main` depending on
  `sorry`;
- `axiom: name: type` for each axiom declared in the checked file;
- the [hole goals](#holes-and-recovery).

`--no-sorry` before any command turneth reachable `sorry` into failure and
refuseth to run a `main` that dependeth on it. axioms stay allowed.

### holes and recovery

each `sorry` recordeth its expected type and named local context. `--check`
printeth `path:line:column:line:column: goal: type`, then indented `name: type`
lines, and the editor showeth the same. goals keep useful definition names,
including recursive calls.

diagnostics may keep independent goals beside a parse or type error. failed
declarations and their dependants stay unavailable, and broken imports provide
no partial names. recovery resumeth at unindented declarations outside
balanced delimiters; unfinished strings, comments, or delimiters may limit it.
running and `--name` require strict checking.

### proof checking

`tung --name name file.tung` auditeth one named declaration, without needing
`main`; qualified imports and private names may be selected. the whole file
must check. its report beginneth `name: …` and `type: …`, listeth the reachable
dependencies, and endeth `name ok` or `name error: …`:

- `axiom`: named axioms, checked against the axiom policy;
- `sorry`: unfinished definitions, a failure under `--no-sorry`;
- `host`: trusted host constants, reported under neither policy.

the closure includeth types, bodies, checking references, selected
dictionaries, host models, and inductive rules across imports, and excludeth
unrelated declarations. a referenced dictionary keepeth all fields and an
inductive family its checked group. private transitive names appear as
`path::name`. a successful audit certifieth a term under its listed
assumptions, not their consistency.

the root manifest may restrict axioms:

```yaml
dependencies: {}
proof:
  axioms: [is~extend]
```

- an absent policy alloweth every axiom; `axioms: []` alloweth none.
- entries resolve to visible axioms by identity. unknown, ambiguous,
  duplicate, and non-axiom entries are errors; a private transitive
  axiom must be made visible before it can be allowed.
- `--allow-axiom name`, repeated before `--name`, replaceth the project policy;
  `--no-axiom` selecteth the empty one. they cannot be combined.
- status 0 meaneth successful checking and audit; anything else returneth 1.

a proof is checked with `--no-sorry`, which faileth only on `sorry` in the
selected closure:

```sh
tung --no-sorry --no-axiom --name zero_+ byspel/walkthrough.tung
```

VS Code's `Tung: Check Proof` auditeth the selected name, or the let at the
cursor, as `--no-sorry --name` with the project policy. it includeth unsaved
sources, showeth the report in `Tung Proof`, and discardeth it if sources
change during checking.
