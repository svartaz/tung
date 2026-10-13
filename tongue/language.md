# tung language reference

audience: agents. purpose: current source syntax and observable behaviour.
[`dependent.md`](dependent.md) owneth checking rules and logical boundaries;
[`development.md`](development.md) owneth implementation and commands.
[`byspel/walkthrough.tung`](../byspel/walkthrough.tung) is the checked introduction.

## files and modules

a `.tung` file containeth declarations. declarations are private unless shown:

- `show let …`, `show ilk …`, and `show flock …` export declarations.
- `show ilk` also exporteth its constructors and eliminator.
- `show name` re-exporteth a visible name; `show ns~name` exporteth it as `name`.
- ordinary `bring` doth not re-export names.

lets, ilks, constructors, flocks, and members share one namespace. each
module declareth a top-level name once. declared names are unqualified.
bookhoard useth `_request` beside constructor `request`, and `hath_naught`
beside member `naught`, to avoid collisions.

## libraries and imports

`bring path.tung alias` importeth a module. the alias is optional; without it,
the last path segment before the first dot is the namespace.

```tung
bring ilk/list.tung
bring ilk/wordbook.tung hashmap

let xs ≔ list~empty
let entries ≔ hashmap~empty
```

- imported names may remain bare when unambiguous. otherwise qualify them.
- two direct imports cannot claim one namespace. imports must be acyclic.
- local names shadow imported bare names, including constructors in patterns.
  qualification still reacheth the import.
- re-exports retain their defining identities. shared dependencies must agree
  on those identities; identical dependencies reached along several paths work.
- missing, conflicting, and cyclic imports are reported at the owning `bring`.

lookup searcheth paths relative to the importing file, declared library roots,
then `TUNG_PATH`. one import path resolving to different files is ambiguous.
`often.tung` is an optional import; there is no automatic prelude.

### manifests

`tung.yaml` declareth local libraries or pinned git repositories:

```yaml
dependencies:
  bookhoard:
    path: bookhoard
  example:
    repo: https://example.org/example.git
    hash: "0123456789012345678901234567890123456789"
    subdir: library
```

- `path` is a live directory, absolute or relative to its declaring manifest.
- `repo` is a git URL or local repository path. `hash` is a full quoted
  40- or 64-digit hexadecimal commit hash. specify both.
- use either `path` or `repo` with `hash`.
- optional `subdir` selecteth a directory within the pinned checkout. it
  cannot contain `..` or escape the checkout through symlinks.
- `bring` paths are relative to the selected library root.

tung findeth the nearest manifest above the source file. each dependency may
have its own manifest. git checkouts live in `.tung/libraries/` beside the
root manifest and work offline after their first fetch.
`tung --library-paths [project-path]` listeth the resolved roots.

resolution checketh the whole dependency graph, including unused libraries.
matching pins or local paths share one root. the following conflict:

- one dependency name with different sources or commits;
- one repository locator and subdirectory with different names or commits;
- one canonical local path with different names.

the root cannot override conflicting indirect pins. different subdirectories
may name different libraries. local paths are canonicalised; relative git
paths are lexically normalised; remote locators are compared as written.
`TUNG_PATH` is outside manifest conflict checking, but duplicate import paths
remain ambiguous.

bookhoard is an ordinary library in [`bookhoard/`](../bookhoard/). an external
project may pin `https://github.com/svartaz/tung.git` at a published hash with
`subdir: bookhoard`.

## names, comments, and literals

most non-space, non-reserved characters may occur in names. punctuation hath
these roles:

| spelling | meaning                             |
| -------- | ----------------------------------- |
| `~`      | imported namespace, as `list~empty` |
| `.`      | field projection, as `person.name`  |
| `^`      | patterns followed by their result   |
| `≔`      | definition                          |
| `*`      | universe, only when standalone      |
| `_`      | discarded input or pattern          |

outside import paths, a name hath at most one `~`, with nonempty, slash-free
parts. `‥`, `·`, `→`, and `=` are ordinary names. there is no general infix
escape. snake_case is the naming convention, including host keys and paths;
`-` remaineth legal. generic polymorphic parameters use Greek letters.
[`anglish.md`](../anglish.md) owneth public terminology.

`#` starteth a line comment; `/* … */` is a non-nested block comment.
`##` and `/** … */` attach documentation to the next declaration.

| literal                  | type      | example           |
| ------------------------ | --------- | ----------------- |
| unsigned integer         | `ℕ`       | `42`              |
| signed integer           | `ℤ`       | `+42`, `-7`, `+0` |
| decimal                  | `float`   | `0.5`, `-2.0`     |
| backtick character       | `unicode` | `` `a ``          |
| single-quoted characters | `string`  | `'hello'`         |

`ℕ` and `ℤ` have arbitrary precision. `+ 1` is application of the name `+`
to natural `1`. natural subtraction stoppeth at naught. characters and strings
accept `\n`, `\r`, `\t`, `\'`, `\\`, and decimal escapes such as `\23383;`.
a character must be one unicode scalar.

## application

functions are curried. in an unmarked sequence, the second term is the
function; the others are arguments in order:

```tung
a f           # f a
a f b c       # f a b c
a f $ g b     # g (f a) b
```

`$` groupeth its left expression and putteth the next function first. `$(…)`
delimiteth such a segment. association works for values and types:

- `<{f, a, b, c}` meaneth `(a f b) f c`.
- `>{f, a, b, c}` meaneth `a f (b f c)`.
- each needeth a function and at least two operands. the marker toucheth `{`.

evaluation is call-by-need: inputs, lets, globals, and constructor fields are
shared and computed when inspected. `match` computeth only its selected branch.
unused `sorry` doth not fail. pure native operations compute their inputs fully.
[deeds](#deeds) perform actions and compute host inputs and results fully.

## declarations and types

types and values use one expression syntax. `*` is a universe with an inferred
level. universes are predicative; authors need not write level parameters.
`[*, *]` is a function from types to types. transparent definitions unfold when
checking equality of types.

### let declarations

```tung
let count ≔ 42
let answer: ℤ ≔ +42
let sameness: [@α: *, x: α, α] ≔ x
let call: [@α: *, @β: *, f: [α, β], x: α, β] ≔ x f
let eke_after: [x:, y: ℤ, ℤ] ≔ x + y
```

`let name ≔ body` inferreth a type. `let name: annotation ≔ body` checketh
against an annotation. its header is one name; inputs belong in the annotation.

- one type annotateth a value.
- brackets describe inputs followed by a final bare result type.
- `name: type` bindeth an input. `name:` inferreth its type from use.
- `pattern: type` destructureth an input; see [patterns](#patterns).
- `_: type` discardeth an input. `_` is never a type.
- bare input types bind no names; the body supplieth their function.
- named and implicit slots precede bare slots. after a named slot, the result
  may be omitted for inference.
- a bracket containing one bare expression is that expression, not a function.
- the neatener writeth `x: α`, with no space before `:` and one after it.

a let's type must be determined. unknown types are never implicitly
quantified: write polymorphic parameters explicitly. all names in an annotation
must already be in scope or bound earlier in that annotation.

`fall inputs, result ^ body` is a function expression with its own annotation.
it needeth at least one input and a final result:

```tung
let sameness ≔ fall @α: *, x: α, α ^ x
let powerset: [α: *, *] ≔ [α, 𝟚]
let wholetale_type: * ≔ ℤ
```

a let returning `*` is an ordinary transparent type function. type functions
may take value inputs or requirements and may be partially applied.
`(term: type)` ascribeth any expression. `α ∏ β` applieth the product type;
`a both b` constructeth a product value.

`→` is defined in `combinator.tung` and re-exported by `often.tung`:

```tung
show let →: [α: *, β: *, *] ≔ [α, β]
```

it hath no special associativity: write `α → (β → γ)`. it may be passed
unapplied, as in `bizen: → semigroupoid`.

### implicit arguments and polymorphism

`@name: type` bindeth an implicit input; `@: type` requireth unnamed evidence.
ordinary type parameters are `@α: *`; a unary type constructor is
`@φ: [*, *]`. these parameters may also range over values.

calls may supply them explicitly. written `@` arguments select parameters in
declaration order, even when written after value arguments. omitted inputs are
inferred or found by [instance search](#flocks-bizens-and-laws). each supplied
input must have its declared type, even when unused.

```tung
let f: [@α: *, @β: *, x: α, _: β, α] ≔ x
'x' f empty
'x' f @string empty
'x' f @string @(string list) empty
```

type inputs are erased before evaluation; implicit value inputs remain runtime
arguments. declared parameters remain in scope in the body and may be forwarded
with `@α`. supplying `@` requireth an implicit parameter in the function's type.

implicit quantifiers may occur at any rank. higher-rank polymorphism needeth annotations:

```tung
ilk pair: * { pair_of: [ℤ, string, pair] }
let both: [f: [@α: *, α, α], pair] ≔ (+1 f) pair_of ('x' f)
let make: [_: ℤ, [@α: *, α, α]] ≔ {x ^ x}
```

`both` requireth one function that worketh for every `α`; each call
instantiateth it independently. `make` returneth such a function. nested
quantifiers scope over their bracket and may shadow outer variables.

### local blocks and recursion

local blocks contain declarations and end with `yield`:

```tung
let seven ≔ (
  let six ≔ +2 · +3
  yield six + +1
)
```

imports, exports, ilks, and foreign bindings are top-level only.
a recursive let needeth an annotation, possibly on its body. its own name
shadoweth imported names in that body; qualification reacheth the import.
an outer local binding of the same name retaineth precedence.

recursion must descend structurally. a call supplieth a checked descendant,
fixed explicit inputs, and explicit indices. trailing other inputs may remain
unapplied; the bare recursive name cannot be passed onwards. mutually recursive
lets are rejected. exact indexed, mutual-family, nested-container, and
function-field rules live under
[pattern matching and recursion](dependent.md#pattern-matching-and-recursion).

well-founded recursion is library code in `ilk/grounded.tung`.
`wellgrounded_selfcall_by` taketh a result motive, measure, well-foundedness
proof, step, and input. the step's recursive call requireth a smaller-measure
proof. `ilk/kindful.tung` provideth `under_wellgrounded`;
`ilk/list_setting.tung` provideth `‥_greatness_under` for list tails.
see [the checked example](../byspel/wellgrounded.tung).

## ilks

`ilk name: signature { constructors }` declareth a family. its signature
endeth in `*`. constructor declarations are comma-separated and state their
full result types:

```tung
ilk list: [α: *, *] {
  empty: α list,
  ‥: [α, α list, α list]
}
```

constructors are curried and must return the declared family at full arity.
header parameters scope over their constructors. a constructor may introduce
its own leading implicit parameters; these cannot redeclare owner parameters.
constructor-only variables are existential when matched and cannot escape.

constructors may select result indices. matching refineth those indices in
that branch:

```tung
ilk tag: [α: *, *] {
  integer: [ℤ, ℤ tag],
  textual: [string, string tag]
}
let unpack: [@α: *, x: α tag, α] ≔ match x {
  n integer ^ n,
  s textual ^ s
}
```

mutually dependent ilks form one group. uniform parameters have compatible
types and visibility; result universes agree. indices may differ. signatures
cannot depend on group members. negative occurrences and cycles through
non-ilk declarations are rejected.

ordinary lists may hold values, types, or type constructors. there is one list
family; [ordinary lists](dependent.md#ordinary-lists) giveth checked examples.

## patterns

`match a, b { rows }` examineth one or more values. `{ rows }` is also a
curried pattern function. each row hath one pattern per input:

```tung
let not: [𝟚, 𝟚] ≔ {yea ^ nay, nay ^ yea}
let chosen ≔ match yea, nay {
  yea, b; b, yea ^ b,
  nay, _ ^ nay
}
let classify: [string, ℤ] ≔ {'yes' ^ +1, _ ^ +0}
```

- `^` separateth patterns from their result. `;` yoketh alternative complete
  rows with one result.
- a variable bindeth once per row; `_` discardeth a value.
- constructors follow ordinary second-is-function order, as `x ‥ leftover`.
- natural, integer, and string literals may be matched exactly.
- rows must be exhaustive and non-redundant. integer and string literal rows
  need a catch-all. `0` with `n heir` covereth all naturals.
- `{}` eliminateth an annotated uninhabited input.
- case functions that destructure constructors need an expected function type.

a named annotation slot may contain a constructor pattern without extra
parentheses: `[a both b: α ∏ β, α]`. literal patterns belong in `match`.
matching `eftbend: a = b` refineth the result; `_: a = b` discardeth the
proof without refinement.

`n heir` matcheth a positive natural and bindeth its predecessor. as a term,
`heir` addeth one unless a constructor of that name is in scope. integer
patterns `n overnaught` and `n heir_undernaught` cover nonnegative and negative
integers; `3 heir_undernaught` is `-4`.

matching a computed scrutinee replaceth its occurrences in the expected result
with the branch constructor. an indexed constructor may also determine fields:
a tail of `α vec 2` hath index `1`. impossible constructors need no row.
index matching supporteth linear constructor shapes; stuck computed indices
are rejected. the [dependent rules](dependent.md#pattern-matching-and-recursion)
state the precise index and descendant restrictions.

`inlook` from `is.tung` also passeth the equation identifying the branch:
`e inlook {p, known ^ body, …}` giveth `known: e = p`. it matcheth a fresh
input rather than refining `e` in place. when its result family cannot be
inferred, supply it: `e inlook @τ @({_ ^ T}) {p, known ^ body, …}`.

### induction

`unbuild name` is the eliminator of an ilk or flock. a single-family
eliminator taketh implicit parameters, motive, constructor methods, indices,
and value:

```tung
let doubled: [l: ℕ list, ℕ list] ≔
  {_: ℕ list ^ ℕ list} unbuild list empty {x, _, leftover ^ x ‥ (x ‥ leftover)} l
```

`name` may be qualified. `unbuild ℕ` and `unbuild =` also work. other names
are rejected. mutual induction taketh one motive per family, then constructor
methods in family and constructor order. nested recursive containers add their
own motives and methods. [inductive declarations and proofs](dependent.md#inductive-declarations-and-proofs)
defineth the method signatures and supported containers.

## fields

an unindexed ilk with one constructor hath a field for each named explicit
constructor input. `value.field` projecteth it; chained access is leftward.

```tung
ilk person: * { person_of: [name: string, age: ℤ, person] }
let someone: person ≔ 'naoki' person_of +35
let older ≔ someone.name person_of (someone.age + +1)
```

separate ilks may share field names. nested constructor brackets extend the
field sequence; later repeated names shadow earlier ones. indexed or
multi-constructor ilks have no fields. there is no anonymous record or update
syntax.

## flocks, bizens, and laws

`flock` declareth a type class; `bizen` defineth an instance. headers end in
`*`, with named parameters and optional `@: parent` requirements:

```tung
flock hath_≍: [α: *, *] {
  let ≍: [α, α, 𝟚]
  let ≍_eftbend: [x: α, (x ≍ x) = yea]
}

bizen: 𝟚 hath_≍ {
  let ≍ ≔ {yea, yea ^ yea, nay, nay ^ yea, _, _ ^ nay}
  let ≍_eftbend ≔ {yea ^ eftbend, nay ^ eftbend}
}
```

- flock parameters omit `@`; members may add local implicit parameters.
- `@: α hath_≍` requireth a dictionary. requirements may be interleaved with
  implicit parameters but may name only preceding parameters.
- a required member is `let name: type` without a body. a law is an ordinary
  member whose type requireth a proof; it hath no separate syntax.
- a bizen head is a flock application in second-is-function order.
  parameters and requirements precede it in one bracket:
  `bizen: [@α: *, @: α hath_≍, (α list) hath_≍] { … }`.
- bizen parameters are implicit. members are lets; each required name occurreth
  once. missing, unknown, repeated, and duplicate instances are rejected.
- member annotations must agree with their flock signatures. members are
  checked in declaration order, regardless of their written order.
- later members may use earlier supplied members. a member's own body referreth
  to its global accessor. recursive methods need ordinary recursive helpers.
- available parent dictionaries take precedence. supplied parent members may
  construct a missing parent inline.

laws concern the actual supplied methods. they are ordinary dictionary fields,
not evaluator rewrite rules. unused law proofs are not evaluated.

search trieth local dictionaries, registered bizens, then inherited instances.
registered bizens use descending priority, then newest first; the first
successful candidate is selected. `bizen 10: …` giveth a priority; the default
is 1000. duplicate instance types are rejected.

`β: * out` marketh an output parameter for search to determine. unknown input
heads postpone search. `bizen fallback: …` may resolve an otherwise stuck
goal; an unsolved goal requireth an annotation. cycles, candidate requirements,
and depth limits are specified under
[flocks and bizens](dependent.md#flocks-and-bizens).

## equality

`bring is.tung` bringeth the ordinary indexed identity type `=` and its sole
constructor `eftbend`; `often.tung` re-exporteth them.
`eftbend` proveth an equation that holdeth by computation. matching it rewriteth
one endpoint to the other. matching equal constructors equateth their fields;
different constructors make the branch impossible. `≍` is Boolean equality;
`≔` defineth a name.

```tung
bring is.tung
let one: ℕ ≔ 1
let checked: one = 1 ≔ eftbend
let evenmete: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔
  match p {eftbend ^ eftbend}
```

`is.tung` also provideth `leibnitz`, `evenmete`, `throughgo`, `throughbear`,
and `inlook`. function extensionality `fall_umtake` is a named axiom.

- `sorry` inhabiteth any expected type as an unfinished assumption. inspecting
  it faileth at runtime; leaving it unused performeth nothing.
- `orsetting name: type` declareth a named axiom without a body. its annotation
  may not bind inputs. it is top-level and may be shown. reaching it at runtime
  faileth with `reached orsetting 'name'`.
- ordinary checking accepteth these assumptions; proof checking auditeth them.
  [logical boundary](dependent.md#logical-boundary) stateth what this entaileth.

### holes and recovery

each `sorry` recordeth its expected type and named local context. `--check`
printeth `path:line:column:line:column: goal: ilk`, followed by indented
`name: ilk` lines. the editor showeth the same goal and context. goals keep
useful definition names, including recursive calls.

diagnostics may retain independent goals beside a parse or type error.
failed declarations and their dependants remain unavailable; broken imports
provide no partial names. recovery resumeth at unindented declarations outside
balanced delimiters. unfinished strings, comments, or delimiters may limit it.
execution and `--name` still require strict checking.

## proof checking

`tung --name name file.tung` auditeth any named checked declaration;
no `main` is needed. qualified imports and private local names may be selected.
the whole file must parse and type-check. a proof is checked with
`tung --no-sorry --name name file.tung`.

the report beginneth `name: …` and `ilk: …`, then listeth the reachable
dependencies, then endeth `name ok` or `name error: …`:

- `orsetting`: named axioms, checked against the orsetting policy;
- `sorry`: unfinished definitions, a failure under `--no-sorry`;
- `host`: trusted host constants, reported independently of either policy.

the closure includeth types, bodies, checking references, selected dictionaries,
host models, and inductive rules across imports. unused unrelated declarations
are excluded. referenced dictionaries retain all fields; inductive families
retain their checked group. private transitive names appear as `path::name`.
a successful audit certifieth a term under its reported assumptions; it doth
not establish their consistency.

the root project's manifest may restrict orsettings:

```yaml
dependencies: {}
proof:
  orsettings: [is~fall_umtake]
```

- an absent policy alloweth every orsetting; `orsettings: []` alloweth none.
- entries resolve to visible orsettings by identity. unknown, ambiguous,
  duplicate, and non-orsetting entries are errors.
- private transitive orsettings must become visible before a policy may allow
  them.
- repeated `--allow-orset name` options before `--name` replace the
  project policy. `--no-orset` selecteth an empty policy; do not combine them.
- status 0 meaneth successful checking and audit; other results return 1.
- `--no-sorry --name` faileth only on `sorry` in the selected closure.

```sh
tung --no-sorry --no-orset --name naught_+ byspel/walkthrough.tung
```

VS Code's `Tung: Check Proof` auditeth the selected name or let at the cursor
as `--no-sorry --name` doth, with the project policy. it includeth unsaved sources and showeth the compiler
report in `Tung Proof`. source changes during checking discard the result.

## deeds

`α deed` is a runner action returning `α`, like haskell `IO` or purescript
`Effect`. evaluating, storing, passing, and combining deeds performeth no action.
performed host inputs and results are computed fully, including constructor
fields; contained functions and deeds remain unperformed.

`deed.tung` provideth ordinary monad operations:

- `sheer` wrappeth a value without an action.
- `warp` changeth the result; `bind` chooseth the next deed from it.
- `then` performeth two deeds and keepeth the latter result.
- `>{then, a, b, c}` performeth several deeds in order.
- `lift₂`, `atfold`, and `each` perform deeds from left to right.
- `deed_steadfast` repeateth a deed; its step receiveth the repeated deed.
  only deeds may use unrestricted looping.

```tung
let main: 𝟙 deed ≔ read bind {
  line some ^ line write_line,
  none ^ 'no input' write_line
}
```

fallible operations return values: `maybe` for absence, or `ε ∑ α` with
`incast₀` for failure and `incast₁` for success. file and process operations
use `string ∑ α`; `read` returneth none at end of input.

library transformers preserve this sequencing:

- `deed/misfaresome.tung`: `ε misfaresome α` wrappeth `(ε ∑ α) deed`.
  `misfare` faileth, `handle` handleth a fault, and `bind` stoppeth at it.
- `deed/hade.tung`: `σ hade α` wrappeth `[σ, (α ∏ σ) deed]`.
  `get`, `put`, and `tweak` read and change the state.
- both provide `lift` and `run`; qualify these when both modules are imported.

## runtime boundary

runnable files declare local `main: 𝟙 deed`; functions and other result types
are rejected. the runner performeth it once, leaving unused definitions alone.
success printeth nothing beyond the program's output. parse, type, and runtime
errors print diagnostics and return status 1. trailing command arguments reach
`arguments`. `exit` endeth the run, or only its task when called inside one.
a final interactive `yield` performeth a deed or fully computeth a value
before printing it.

`--check` and `--check-stdin` check a module or a program: a file without
`main` is a module, and a `main` it declareth must be runnable as above. they
return 0 after successful checking and 1 on rejection. their output includeth:

- `ilk ok` after success;
- `sorry: name` for shown declarations, bizens, or `main` depending on `sorry`;
- `orsetting: name: ilk` for orsettings declared in the checked file;
- the recorded [hole goals](#holes-and-recovery).

`--no-sorry` turneth reported `sorry` dependencies into failure and refuseth
execution when `main` dependeth on them. it still alloweth orsettings.

an annotated top-level let may bind a foreign operation:

```tung
let write: [string, 𝟙 deed] ≔ 'write' fremmed
let eke_kindful: [ℕ, ℕ, ℕ] ≔ 'eke_kindful' fremmed {
  m, 0      ^ m,
  m, k heir ^ (m eke_kindful k) heir
}
```

the string key and complete type must match the host catalogue. bindings with
no arguments need a deed type. a pure operation may supply a checked structural
model after `fremmed`; deed operations cannot. named annotation inputs require
a model. literal inputs compute natively during checking; other inputs unfold
the model. the runner always useth the native operation.

`ℕ`, `ℤ`, `float`, `unicode`, and `string` are primitive types. their
operations and bizens come from explicit library imports, usually
`often.tung`. `deed` and `task` are opaque primitive families of kind
`[*, *]`; they have no constructor or eliminator. tasks are controlled by
`fork`, `wait`, `wait_for`, and `outstrike`.

host data families such as `list`, `maybe`, `wordbook`, and `𝟙` are the
ordinary ilks declared at their bookhoard paths. a same-spelled ilk elsewhere
is a different type. [host binding rules](dependent.md#deeds-and-host-bindings)
state their required schemas; the [bookhoard reference](../bookhoard/reference.md)
owneth library contracts.
