# tung language reference

audience: agents. purpose: everything a program author writeth and observeth:
syntax, names, modules and manifests, the meaning of each construct, the
runner, and command-line output. [`dependent.md`](dependent.md) owneth how the
checker realiseth these rules; [`development.md`](development.md) owneth the
implementation.

## files and modules

a `.tung` file containeth declarations. a runnable file declareth local
`main: 𝟙 deed`. the runner performeth that deed; see [deeds](#deeds).

declarations are private by default. `show` publisheth a declaration.
`show ilk` publisheth the family and its constructors; its eliminator
followth the family. `show
name` re-exporteth the visible declaration spelled `name`; `show ns~name`
publisheth it as `name`. ordinary `use` doth not re-export anything.

lets, ilks, constructors, flocks, and flock members share one namespace. a
module declareth each top-level name once, so a flock and its member, or an
ilk and its constructor, need different names; bookhoard prefixeth such a
flock with `hath_` and such a type with `_`.

## libraries and imports

`use path` importeth a module. its final path segment, up to the first dot,
becometh the default namespace. an optional final name replaceth it.

```tung
use ilk/list.tung
use ilk/table.tung hashmap

let xs ≔ list~empty
let entries ≔ hashmap~empty
```

visible imported names may remain bare when unambiguous. two different direct
imports cannot claim the same namespace. the import graph must be acyclic. a
local term shadoweth an imported bare term in value and application positions. a
qualified name still reacheth the import.

re-exported names retain their defining identities. ambiguous bare names
must be qualified with a direct import namespace; diagnostics suggest those
visible namespaces. a missing or cyclic use is reported at its importing
statement, in the module containing that statement.

cached modules must agree on every shared defining identity, including
transitive dependencies. different definitions of one identity are rejected
at the incoming `use`; an identical dependency reached along two paths is
accepted.

the host catalogue explicitly overloadeth primitive names, such as `+` for
integer and float, within primitive scope. direct application trieth their
signatures in catalogue order. as a value, the name selecteth the first signature.
a local value shadoweth an imported constructor of the same spelling, in
patterns too: there the name bindeth a variable, and a qualified name still
reacheth the constructor.

module lookup searcheth paths relative to the importing file, declared library roots,
then `TUNG_PATH` entries. a `.tung` path resolving to different files is
ambiguous. `ground.tung` is an optional import, not a prelude.

### manifests

the standard library is an ordinary library in [`bookhoard/`](../bookhoard/).
a `tung.yaml` manifest declareth local library paths or pinned git repositories
under `dependencies`:

```yaml
dependencies:
  bookhoard:
    path: bookhoard
  example:
    repo: https://example.org/example.git
    hash: "0123456789012345678901234567890123456789"
    subdir: library
```

each dependency key nameth one library throughout the graph, not a local alias.
`path` giveth a live directory relative to the declaring manifest, or an
absolute directory. it need not be a git repository. changes there take effect
without a commit. `repo` giveth a git URL or local git repository path, such as
`../my-library`. `hash` giveth its full 40- or 64-digit hexadecimal commit hash.
quote a hash so yaml readeth an all-digit value as text. specify either `path`
or both `repo` and `hash`. an optional `subdir` selecteth a library inside the
pinned checkout. it must stay inside that checkout, even through symlinks.
omit `subdir` when the repository root is the library. external projects may
pin Bookhoard with `repo: https://github.com/jukisima/tung.git`, a published
commit hash, and `subdir: bookhoard`. `use` paths name `.tung` files relative to
the selected library root.

tung findeth the nearest `tung.yaml` above the source file. local paths are
resolved from the manifest that declareth them. git pins are checked out under
`.tung/libraries/` beside the root manifest. after the first fetch, tung
reuseth the checkout offline. `tung --library-paths [project-path]` listeth the
resolved roots. `TUNG_PATH` addeth roots outside manifest resolution.

each library may declare `tung.yaml`. tung traverseth the whole dependency graph,
including libraries the program doth not import. matching git pins share one
checkout; matching local paths share one root. before module checking, tung
rejecteth:

- one name with different sources, including a path and a git pin;
- one repository locator and subdirectory with different names or commits;
- one local path with different names.

if two libraries pin `shared` to different commits, the project faileth. the
root manifest cannot override either pin. two names for one repository also
conflict when they select the same subdirectory, even at the same commit.
different subdirectories of one repository may supply distinct libraries.

relative git repository paths resolve from the manifest that declareth them and
are lexically normalised. local library paths are canonicalised, so aliases to
one directory count as one path. remote locators are compared as written.
`subdir` is normalised and cannot contain `..`. use the same name and source in
every manifest. `TUNG_PATH` roots lie outside manifest conflict checking. the
same `.tung` path in different roots remaineth ambiguous when imported.

## nonstandard keywords

tung nameth several features with anglish words. each word below is a keyword
or a contextual word with the meaning of the general term.
[`anglish.md`](../anglish.md) listeth every anglish word, including library
names such as `warp`, `sheer`, `heir`, and `hath_+`.

| tung        | general term     | use                                       |
| ----------- | ---------------- | ----------------------------------------- |
| `ilk`       | data type        | `ilk name: kind { constructors }`         |
| `flock`     | type class       | `flock name: [parameters, *] { members }` |
| `bizen`     | instance         | `bizen: type { definitions }`             |
| `fallback`  | default instance | `bizen fallback: type { … }`              |
| `deed`      | io action        | `α deed`                                  |
| `fremmed`   | foreign binding  | `let name: type ≔ 'key' fremmed`          |
| `orsetting` | axiom            | `orsetting name: type`                    |
| `fall`      | function         | `fall inputs, result ^ body`              |
| `unbuild`   | eliminator       | `motive unbuild name methods worth`       |
| `show`      | export           | `show let …`, `show a, b`                 |
| `use`       | import           | `use path.tung alias`                     |
| `yield`     | block result     | `(let … yield result)`                    |

the project's own names follow the same direction: `tongue` is the compiler,
`bookhoard` the standard library, and `byspel` the examples.

## names, comments, and literals

most non-space, non-reserved characters may occur in names. `~` qualifieth
imports; `.` selecteth record fields; `^` separateth a match case's patterns from its
result. type alias, data, and flock names are unqualified. so are their
constructors and members. outside `.tung` import paths, a name may contain at
most one `~`. its namespace and member must be nonempty and slash-free. `‥` is
an ordinary name; there is no general infix escape. `_` discardeth a binding or
match value.

names, keywords, host keys, and `.tung` paths use snake_case: words are
lowercase and joined by `_`, as in `to_text`, `warp_flat`, and
`flock/order/hath_at_most.tung`. `-` remaineth a legal name character, so this is
a convention, not a lexical rule.

`#` starteth a line comment. `/* ... */` formeth a non-nested block comment. `##`
and `/** ... */` attach doc comments to the next declaration. editor help and
generated bookhoard pages use them.

an integer literal of type `ℤ` always hath a sign: `+42`, `-7`, `+0`. unsigned
digits such as `42` are a natural number of type `ℕ`. both are arbitrary
precision; the compiler storeth naturals as haskell `Natural`. `+ 1` with a space
is the name `+` applied to the natural `1`. `ℕ` subtraction stoppeth at zero:
`2 - 3` is `0`. a quantity that cannot be negative is a `ℕ`: counts, indices,
durations in milliseconds, ports, exit codes, http status codes, and unicode
code points. float literals contain a decimal point and an optional `-`. a
backtick introduceth one unicode scalar, and single quotes delimit text. both literal forms accept `\n`, `\r`, `\t`, `\'`, `\\`, and
decimal escapes such as `\23383;`.

## application

every function is curried. in an unmarked sequence of two or more terms, the
second is the function. the others are arguments in order.

```tung
a f           # f a
a f b c       # f a b c
a f $ g b     # g (f a) b
```

`$` groupeth its left expression and useth the next atom as the function. `$(`
starteth a function-first segment.

`<{f, a, b, c}` lowereth to `(a f b) f c`. `>{f, a, b, c}` lowereth to
`a f (b f c)`. each requireth a combining function and at least two values. `r{`,
`<{`, and `>{` are single opening delimiters. the brace must touch the
marker.

runtime evaluation is call-by-need. application arguments, local `let`
values, globals, record fields, and constructor fields are computed when
inspected and shared thereafter. unused values are not computed. `match`
inspecteth its scrutinee and computeth only its selected branch; recursive
hypotheses follow the same rule. a failure value, such as `sorry`, faileth
when inspected. pure native operations compute their inputs fully. host
deed inputs and deed results are computed fully when the deed is performed.
building a deed performeth no action.

## declarations and types

`ilk name:signature {constructors}` declareth a data type. the signature is `*`
for a type without parameters, or a bracket of kinded parameters ending in `*`,
as in `[a: *, *]`. `*` is a universe with an inferred level. `[*, *]` is a function type from
types to types. only a standalone `*` is universe syntax. names such as `‥` remain
ordinary names. the magma operation is `·`.

constructors are comma-separated, and every constructor stateth its type, as in
a GADT: `name:type`. a bracketed type listeth optional `@` parameters, the
field types, and the result type; a single type is the result alone, as in
`none: a maybe`. fields are bare types, as in `some: [a, a maybe]`. the
result type must name the declared `ilk` with its full arity. a constructor without a type is an error.

```tung
ilk list: [a: *, *] {
  empty: a list,
  ‥: [a, a list, a list]
}
```

constructors may choose different result indices. a match refineth each index
within its own case. a type variable used only by a constructor is existential;
it cannot escape that case.

```tung
ilk tag: [a: *, *] {
  integer: [ℤ, ℤ tag],
  textual: [text, text tag]
}
let unpack: [@a: *, x: a tag, a] ≔ match x {
  n integer ^ n,
  t textual ^ t
}
```

### let declarations

`fall slots, result ^ body` writeth a typed function as an expression. its
items are product slots; the last is the result type, `^` followeth, and the
body extendeth to the end of the expression. a bare slot bindeth no name, and
`fall` requireth at least one input, so `fall * ^ *` is rejected.

```tung
let is ≔ fall @α: *, a: α, α ^ a
let powerset ≔ fall α: *, * ^ [α, *]
```

`let name ≔ body` bindeth a name. `let name:annotation ≔ body` also annotateth
it. the header is only the name; arguments are named slots of the annotation.
a slot with no type after its `:` is inferred from the body, so
`let hath_+: [x:, y: ℤ, ℤ] ≔ x + y` inferth `x: ℤ`. `_` is never a type; it only
discardeth an input. a let's type must be fully determined: a let is never
generalised over unknown types, so a polymorphic let writeth its parameters,
as `let selfness: [@α: *, x: α, α] ≔ x`.

```tung
let count ≔ 42
let answer: ℤ ≔ +42
let selfness: [x:] ≔ x
let selfness: [@a: *, x: a, a] ≔ x
let selfness: [@a: *, a, a] ≔ {x ^ x}
let eke_after: [x:, y: ℤ, ℤ] ≔ x + y
```

an annotation is one type or a bracketed list of slots:

- one type annotateth a value.
- a bracket list holdeth `@name:kind` type parameters and `@:flock`
  requirements, then value slots, as described below.
- a bracket with one bare expression is that expression; without an input it
  introduceth no function argument.
- `pattern:type` is a named slot. it bindeth an argument for the body. its
  pattern followeth the second-is-function rule and needeth no grouping, as in
  `let unbox:[@a:*, x box:a box, a] ≔ x` and `a both b`. a slot named by a
  constructor without fields matcheth that constructor, so
  `let evenmete:[@α:*, @a:α, @b:α, backbend:a = b, b = a] ≔ backbend` rewriteth
  `b` to `a` in the result. the match itself is the evidence: `_:a = b` doth
  not inspect the proof, so `b` stayeth distinct from `a`. slot patterns never match literals; use `match`.
- a bare slot giveth a type only and bindeth no name. the body supplieth bare
  arguments, usually with an anonymous function. named slots precede bare
  slots.
- the final bare slot is the result type. after a named slot, omit it to
  infer the result.
- `_:type` as a slot discardeth an argument.
- the formatter writeth `:` with no space before and one space after: `x: α`.
- an annotation must be followed by `≔`.

an annotation endeth in a kind declareth a type alias; see
[type expressions](#type-expressions).

use Greek letters for generic polymorphic parameters. type and flock names
carry no `*` prefix, and no term reuseth a type's name: name a slot `l`, not
`list`, beside `list`. when a constructor would share its type's name, the
constructor getteth a new name (`both` with `both`, `complex` with `+i`, `nonempty`
with `‥′`), or, for a type with one constructor, the type taketh a `_` prefix
(`_request` with `request`). a flock whose member would share its name taketh a
`hath_` prefix (`hath_zero` with `zero`). `*name` still lexeth as one name, and
standalone `*` is syntax.

leading `@name:kind` declareth a polymorphic type parameter. use `@a:*` for
an ordinary type and `@f:[*, *]` for a unary type constructor.
type declarations use `name:kind` without `@`.
every type variable in a written annotation must be declared or already in
scope, including type constructor variables. a
requirement nameth only parameters declared before it.
unknown names are errors. an unannotated `let selfness: [x:] ≔ x` may still infer
a polymorphic type.

an anonymous function bound by `let` may call itself, with or without an
annotation. other initialisers see preceding bindings, including a preceding
binding with the same name. an unguarded self-reference is an error.

data, alias, and flock parameters scope over their declarations.
flock methods, constructors, and laws may introduce local leading `@` parameters.
local parameters cannot redeclare their owner parameters.
an instance's type listeth its variables and requirements before its head:
`bizen:[@a:*, @:a hath_≍, (a list) hath_≍] {...}`.
these variables scope over its head, requirements, and members. a constructor such as
`pack [@a:*, a, packed]` declareth an existential payload when matched.

calls may supply declared implicit parameters explicitly, including values. `@text` passeth a named
type; `@(text list)` passeth a compound type. type arguments select header
parameters in declaration order, regardless of their position among value arguments. omitted trailing type
arguments are inferred. each supplied type must have the declared parameter's
kind, including when the parameter is unused. type inputs are erased before evaluation; implicit value inputs remain runtime
arguments:

```tung
let f: [@a: *, @b: *, x: a, _: b, a] ≔ x
'x' f empty
'x' f @text empty
'x' f @text @(text list) empty
```

declared type parameters are in scope in the body. a call may forward them
with `@a`. explicit type input requireth a declared header parameter or a value
with an explicitly quantified type.

inside a function type, leading `@name:kind` bindeth an explicit universal
quantifier. its scope is that bracketed type. quantifiers may occur in arguments
or results, at any rank:

```tung
let both: [f: [@a: *, a, a], r{number: ℤ, word: text}] ≔
  r{number≔+1 f, word≔'x' f}
let make: [_: ℤ, [@a: *, a, a]] ≔ {x ^ x}
```

`both` requireth a function that worketh for every `a`. each use of `f`
instantiateth it independently. `make` returneth such a function. a monomorphic
function cannot satisfy either quantified type. nested binders shadow outer
type variables; other free variables retain their outer meaning.

higher-rank types require explicit annotations. universe constraints enforce
predicativity; inferred type inputs may themselves be function types. passing an anonymous function checketh its arguments against the expected
signature. type inputs create no runtime arguments. requirements are implicit dictionary
inputs and may occur in nested products.

local blocks are parenthesised and end with `yield`.

```tung
(
  let six ≔ +2 × +3
  yield six + +1
)
```

### type expressions

type application useth second-is-function syntax.
`ℤ list` applieth `list` to `ℤ`; `a both b` applieth the binary product type.
a let returning `*` defineth a transparent type function, as in
`let powerset:[a:*, *] ≔ a → 𝟚`. `let count:* ≔ ℤ` defineth a transparent
constant. types and values use one expression syntax. type functions may take
value inputs and requirements; partial application followeth ordinary function
application. conversion unfoldeth transparent definitions.

function types use `[argument, result]`. nested brackets describe function
arguments. `→` is an ordinary name, not syntax. `combinator.tung` defineth it,
and `ground.tung` showeth it:

```tung
show let →: [α: *, β: *, *] ≔ [α, β]
```

`a → b` is ordinary type application, so it hath no associativity: write
`a → (b → c)`. because its body applieth the function type constructor to its
parameters, `→` may be passed unapplied to a flock, as in
`bizen: → semigroupoid`. `(term:type)` constraineth any term.

```tung
let powerset: [a: *, *] ≔ a → 𝟚
let call: [@a: *, @b: *, f: [a, b], x: a, b] ≔ x f
let answer ≔ (+1 + +2: ℤ)
```

a local alias of a function parameter retaineth its type constraints.

a let whose body nameth itself is recursive, even when an import of that name
is visible: a top-level let shadoweth the import in its own body as everywhere
else, so `use source.tung let worth ≔ source~worth + +1` extendeth the import
by qualification. only an outer local binding of that name hideth the let's
own name. a recursive let needeth an annotation, or an ascribed body such as
`let f ≔ (body: [ℕ, ℕ])`. recursion must be structural; see
[dependent.md](dependent.md#pattern-matching-and-recursion).

### composition and lists

`<{f, a, b, c}` and `>{f, a, b, c}` work in type expressions as well as
terms. they expand to `(a f b) f c` and `a f (b f c)`, respectively.
composition hath no special list rules. native type-list kinds and operators
have been removed. the compiler useth one ordinary list family for
values, types, and type constructors. see
[dependent lists](dependent.md#ordinary-lists) for checked examples and indices.

## algebraic data and patterns

`ilk` declareth an algebraic data type. type parameters and constructor arguments
follow the ordinary sequence rule.

```tung
ilk maybe: [a: *, *] {
  none: a maybe,
  some: [a, a maybe]
}
```

constructor application is curried. patterns may bind variables, use `_`, match
exact natural, integer, or text literals, or destructure constructors. `n heir`
matcheth a positive natural and bindeth its predecessor, so `0` and `n heir`
together cover `ℕ`, and a function on `ℕ` may recurse on `n`. as a term,
`heir: [ℕ, ℕ]` addeth one, unless a constructor named `heir` is in scope.
`ℤ` is built the same way from `n overnaught`, which is `n`, and
`n heir_undernaught`, which is `-(n + 1)`; the two cover `ℤ`, and
`3 heir_undernaught` is `-4`.
each binder may occur only once in a pattern row.

`match` consumeth one or more comma-separated scrutinees. `{...}` formeth an
anonymous function with one curried input per pattern. `^` separateth a case from
its result. `;` joineth complete alternative rows that share a result. when a
scrutinee is a computation, such as `a ≤ a`, each row's expected type hath
that row's constructor in its place, so `match a ≤ a {yea ^ reflect, nay ^
reflect}` proveth a statement about `a ≤ a` by cases. the
[dependent rules](dependent.md#inductive-declarations-and-proofs) give the
exact conditions.

`match e for known { rows }` nameth the equation between one scrutinee and
each pattern. in a row whose pattern is `p`, `known` hath type `e = p`, so a
branch can use what the match learned about a computed scrutinee. it matcheth
a fresh copy of `e`, as lean's `match h : e with` doth, so `e` itself is not
refined in place. `for` endeth the scrutinee only in a match header; elsewhere
it is an ordinary name. a match with more than one scrutinee cannot name an
equation.

```tung
let chosen ≔ match yea, nay {
  yea, b; b, yea ^ b,
  nay, _ ^ nay
}

let not: [𝟚, 𝟚] ≔ {
  yea ^ nay,
  nay ^ yea
}

let classify: [text, ℤ] ≔ {
  'yes' ^ +1,
  _ ^ +0
}
```

the checker rejecteth non-exhaustive and redundant rows over algebraic data.
finite rows of integer or text literals need a variable or `_`, as these types
have infinitely many values. natural rows may instead end with `n heir`. an empty function `{}` eliminateth an annotated
uninhabited input such as `𝟘`.

`unbuild name` is the eliminator of the ilk or flock `name`, as a term. it taketh
a motive, one method per constructor, and the value, so a proof by
structural induction is written with the motive first:

```tung
let doubled: [l: ℕ list, ℕ list] ≔
  {_: ℕ list ^ ℕ list} unbuild list empty {first, _, rest ^ first ‥ (first ‥ rest)} l
```

`name` may be qualified, and `unbuild ℕ` and `unbuild =` name the primitive
eliminators. any name that is not an ilk or flock is rejected. the
[dependent rules](dependent.md#inductive-declarations-and-proofs) define the
method types.

## records

records are closed. `r{field:type}` formeth a type; `r{field ≔ worth}` formeth a
value. an update placeth its base after `≔`. later entries set or remove fields.

```tung
let person: r{name: text, age: ℤ} ≔
  r{name ≔ 'naoki', age ≔ +35}
let older ≔ r{≔ person, age ≔ +36}
let public ≔ r{≔ person, - age}
let age ≔ older.age
```

in `record.field`, `record` is a term and `field` an unqualified field name.
access chaineth leftward: `record.outer.inner` selecteth `outer`, then `inner`.
field sets must match an annotated record type. duplicate labels, unknown field
removal, and non-record updates are errors.

## flocks, bizens, and laws

the [keyword table](#nonstandard-keywords) giveth the general terms for
`flock` and `bizen`.

`flock name:[parameters, @:parent, *] {...}` declareth a flock. its signature
listeth `name:kind` parameters and `@:parent` requirements and endeth in `*`;
`flock name:* {...}` hath no parameters. `a:*` declareth a type parameter.
`f:[*, *]` declareth a unary type constructor parameter.

`bizen:head {...}` provideth evidence and member implementations. the head keepeth
second-is-function order: `bizen:ℤ convert text {...}`. a bizen with
parameters or requirements writeth them before the head in one bracket:
`bizen:[@a:*, @:a hath_≍, (a list) hath_≍] {...}`.

`@:a hath_≍` in a header stateth required evidence. requirements and `@`
parameters precede value arguments, in any order among themselves, but a
requirement nameth only parameters declared before it. flock and bizen headers
have no value arguments. a required member is `let name:type` with no body; a
function member writeth its inputs and result in brackets. a law is a named
member whose type is an equality on terms: `let name:[binders, left = right]`
bindeth typed patterns and endeth in its equation. a law hath no body.

```tung
flock hath_≍: [a: *, *] {
  let ≍: [a, a, 𝟚]
  let backbend: [x: a, (x ≍ x) = yea]
}

let ≭: [@a: *, @: a hath_≍, a: a, b: a, 𝟚] ≔ (a ≍ b) if nay yea

flock applicative: [f: [*, *], @: f functor, *] {...}
bizen: [@b: *, @: b ring, @a: *, [a, b] ring] {...}

bizen: 𝟚 hath_≍ {
  let ≍ ≔ {
    yea, yea ^ yea,
    nay, nay ^ yea,
    _, _ ^ nay
  }
  let backbend ≔ sorry
}
```

`=` is the [identity type](#equality) in scope, applied under the
second-is-function rule: each side is one term, so a compound side needeth parentheses, as in
`(a ∧ a) = a`. law brackets require a type for each pattern. a law name shareth the flock's member
namespace, so it cannot repeat a member or another law. `let` implementations inside `bizen`
use ordinary declaration syntax.

a bizen must supply each required member not supplied by a parent. a child bizen
also witnesseth required parent flocks and may define inherited members.
duplicate bizens are incoherent.
an annotated member must satisfy its own signature and the required method type. a member that nameth
itself refereth to the flock, found by instance search; the bizen is not yet
registered while its members are checked, so a recursive member is a
recursive let that the member nameth, as `let ∋ ≔ holds` in
`ilk/list.tung`.

selection useth local requirements, registered bizens, then inherited
instances, as lean doth. registered bizens are tried by priority, higher
first, and the latest declared first among equals; the first that matcheth,
with its own requirements, is chosen. `bizen 10: …` writeth a priority; the
default is 1000. inherited search useth the first matching path.

a flock parameter written `β: * out` is an output: search findeth it, as
lean's `outParam` doth. a goal waiteth while the head of an input parameter is
unknown. a goal still stuck on an unknown input trieth the flock's fallback
bizens, written `bizen fallback: …`, as lean's default instances; for
example the function `category` bizen is a fallback, so `is` used as a
function findeth it. without a fallback, the goal needeth an annotation or
stayeth unsolved, and the let needeth an annotation.
[dependent instance search](dependent.md#flocks-and-bizens) defineth cycles,
depth, waiting goals, and candidate requirements.

## equality

`x = y` is the type of proofs that `x` and `y` are equal; both sides share one
type. `=` and `backbend` are primitive and visible in every module, like `ℕ`.
bookhoard's `is.tung` proveth the lemmas `leibnitz`, `evenmete`,
`throughgo`, and `transport`.

its only constructor is `backbend: [@α: *, @x: α, x = x]`, so `backbend`
proveth any equation that holdeth by computation. a proof of `x = y` may be
matched against `backbend`, which rewriteth `y` to `x` in that branch. when
both sides are built from constructors, matching compareth them: matching
constructors equate their fields, so `backbend: (a ‥ l) = (b ‥ m)` giveth
`a = b`, and different constructors make the match empty, so
`[yea = nay, 𝟘] ≔ {}` holdeth. `≍` is
boolean equality, a flock member that computeth `yea` or `nay`; `≔` defineth a
name and is not an equation.

```tung
let one: ℕ ≔ 1
let checked: one = 1 ≔ backbend
let evenmete: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔
  match p { backbend ^ backbend }
```

a law statement is a type over the flock's members. each bizen proveth every
law of its flock, and also the laws of each parent flock it witnesseth because
that parent hath no bizen of its own. a proof is checked against the law with
this bizen's own members, so a law about `≍` is stated for the bizen's `≍`:

```tung
bizen: 𝟚 hath_≍ {
  let ≍ ≔ ...
  let backbend ≔ {x ^ ...}
}
```

a law is an ordinary member whose type is an equation. a missing law is an
error, and `sorry` assumeth one. the compiler neither executeth nor rewriteth
with laws. a law name is a top-level accessor like any member name, so
`rule @α x` is a proof term, and a flock requirement carrieth its laws: a
proof may use a required dictionary's laws as evidence. two flocks cannot
share a law name.

`sorry` is a term of any type. it standeth for an omitted proof or definition.
inspecting it is a runtime error. an uninspected `sorry` never faileth, even
as a top-level `let`. it is an unchecked assumption, not a proof. the
[logical boundary](dependent.md#logical-boundary) defineth this limitation.

`orsetting name: type` declareth a named assumption: a constant of that type
without a proof. it is top-level and may be shown; its annotation must be a
type and may not bind inputs. checking never unfoldeth it, and reaching it at
run time faileth with `reached orsetting 'name'`. an `orsetting` is a deliberate,
listed assumption, such as an axiom a proof relieth on; `sorry` remaineth an
unfinished hole.

each `sorry` is also a hole. checking recordeth its goal, the type expected
there, and its named context, the locals in scope with their types, outermost
first. a pattern variable showeth under its own name. `--check` printeth each
goal after the `sorry` lines as `path:line:column:line:column: goal: type`,
followed by one indented `name: type` line per local, and the editor showeth
the same text as information at the hole and in hover. a goal keepeth each definition
by name unless unfolding it reacheth a constructor, literal, record, or
variable, and a recursive call keepeth its name, so a goal readeth
`(first ‥ (rest · (b · c))) = (first ‥ ((rest · b) · c))`.

## deeds

`α deed` is an action that yieldeth an `α` when performed, like haskell `IO` or
purescript `Effect`. `deed` is a primitive type constructor of kind `[*, *]`.
it is a reserved keyword for editors and metadata but lexeth as an ordinary
name, so `α deed` is type application.

evaluation never performeth a deed. building, storing, passing, or combining
deeds performeth nothing. performing a deed computeth values fully: a host deed's
inputs are computed fully before the host acteth, and the result of each
performed deed is computed fully before the next step receiveth it. fully
computed meaneth every constructor field, record field, and literal is
computed; functions and deeds inside the value stay as they are. so
`let main: 𝟙 deed ≔ 40 fibonacci $ to_text $ write_line` computeth the number
when `main` writeth it, and an accumulator passed between the steps of a
`deed_fix` loop doth not build a chain of pending work. the runner performeth
`main`. interactive evaluation performeth a deed only when it is the final
`yield`, as a repl prompt doth; a yielded value is computed fully before it
printeth.

deeds compose only through bookhoard's monad methods; there is no sequencing
syntax. `deed/action.tung` provideth `deed functor`, `deed applicative`, and
`deed monad`, built on the host bindings `deed_sheer` and `deed_bind`:

- `sheer` wrappeth a value in a deed that performeth nothing;
- `warp` changeth a deed's result;
- `warp_flat` passeth a deed's result to the function that chooseth the next deed;
- `then` performeth two deeds in order and keepeth the second result;
- `>{then, a, b, c}` performeth several deeds in order;
- `lift₂` and `apply` perform their deeds from left to right;
- `each` performeth an action for each list element in order;
- `deed_fix` repeateth a deed: its step receiveth the repeated deed itself, so
  `{again ^ read deed_bind {none ^ only deed_sheer, _ some ^ again}} deed_fix`
  readeth until input endeth.

```tung
let greet: [name: text, 𝟙 deed] ≔ ('hello, ' write) then (name write_line)

let main: 𝟙 deed ≔ read warp_flat {
  line some ^ line greet,
  none ^ 'no input' write_line
}
```

nothing throweth. a fallible operation returneth a value. `maybe` is used when
absence explaineth the failure. `text ∑ α` is used when a message doth:
`incast₀` carrieth the message and `incast₁` the result.

- `%`, `from_text`, `to_ℕ`, `natural_to_unicode`, `⌊` of a non-finite float,
  and list `at` return `maybe`;
- `read` yieldeth none at the end of input;
- `file~read`, `file~write`, `file~append`, and `process~run` yield `∑`;
- `environment` yieldeth none for an unset variable;
- `wait` yieldeth none for a cancelled task, and `wait_for` also yieldeth none
  after its timeout;
- `serve` yieldeth a message when the server stopeth.

## runtime boundary

`main` must have type `𝟙 deed`. the checker rejecteth any other type, including
a function from `𝟙`. the runner performeth `main` once and leaveth unused
top-level definitions unevaluated. it printeth nothing of its own on success; a parse, type, or runtime
error is printed and the exit status is 1. `tung file.tung args…` passeth the
trailing arguments to `arguments`. `exit` endeth the whole run with its status;
inside a task it endeth only that task, which then hath no result.

`--check`, `--check-module`, and `--check-stdin` return status 0 only after
successful checking. a rejected source returneth status 1. after `type ok`,
each line `sorry: name` nameth a shown declaration, bizen, or `main` of the
checked file whose body useth `sorry`, directly or through any definition it
useth. a bizen whose law is `sorry` is listed as `sorry: bizen type`. a host binding is a program, not an assumption.
`--no-sorry` before the command turneth any such assumption into a failure:
the lines are printed and the status is 1. it also refuseth to run a program
whose `main` assumeth `sorry`. each line `orsetting: name: type` then nameth an
`orsetting` declared in the checked file; `--no-sorry` allowth them. the goal of
each `sorry` followeth, as described under [`sorry`](#equality).

an annotated file-level `let` may bind a host operation. a text key precedeth
`fremmed`. the host key and full declared type must match the compiler
catalogue. a host binding without arguments must have a deed type; performing
the deed runneth the host action. `_foreign.tung` and the `deed/` modules
declare the runner's deeds: console text, `random`, tasks, `sleep`, files,
arguments, environment, `exit`, the clock, processes, the web server, and
`deed_fix`. every pure host operation hath one definition, shared by the
erased evaluator and normalising kernel.

a pure host operation may give a model after `fremmed`, a body checked
against the annotation like any let body:

```tung
let eke_natural: [ℕ, ℕ, ℕ] ≔ 'eke_natural' fremmed {
  m, 0         ^ m,
  m, k heir ^ (m eke_natural k) heir
}
```

a call of the binding's own name in the model is structural recursion. the
annotation may bind inputs only when a model followeth. checking computeth
natively when every input is a literal and unfoldeth the model otherwise, so a
proof can reason about the operation, as `[n: ℕ, (n + 0) = n] ≔ backbend`;
goals show the model under the binding's name. the runner always useth the native
operation. a deed operation cannot have a model.
`ilk/natural.tung` modelth `ℕ` equality, order, addition, subtraction, and
multiplication, and `ilk/integer.tung` the same `ℤ` operations and the
conversions `to_ℕ` and `to_ℤ`. universe parameters that a model gaineth
from instance search but its type doth not mention are set to zero.

the compiler provideth no operation or bizen by itself. `ℕ`, `ℤ`, `float`,
`unicode`, and `text` are primitive types, but every operation on them,
including `+` and `≍`, is a `fremmed` binding wrapped by a bookhoard bizen;
`ilk/natural.tung`, `ilk/integer.tung`, and `ilk/float.tung` declare the
numeric ones. a program that useth arithmetic therefore importeth bookhoard,
usually through `ground.tung`.

`deed` and `task` are opaque primitive families of kind `[*, *]`. only the
runner startth a task. they have no data constructor or eliminator;
`fork`, `wait`, `wait_for`, and `cancel` are their operations.

a host data type, such as `maybe`, `list`, or `𝟙`, is the `ilk` of its name
declared in its bookhoard file, such as `ilk/maybe.tung`. an `ilk` of the same
name elsewhere is a different type, whatever its constructors.
the required constructor and field schemas are described under
[dependent host bindings](dependent.md#deeds-and-host-bindings).

the
[bookhoard reference guide](../bookhoard/reference.md)
explaineth the standard library's design boundaries. runnable examples live under
[`byspel/`](../byspel/).
