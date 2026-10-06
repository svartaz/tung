# tung language reference

audience: agents. purpose: everyþing a program author writeþ and observeþ:
syntax, names, modules and manifests, þe meaning of each construct, þe
runner, and command-line output. [`dependent.md`](dependent.md) owneþ how þe
checker realiseþ þese rules; [`development.md`](development.md) owneþ þe
implementation.

## files and modules

a `.tung` file containeþ declarations. a runnable file declareþ local
`main: 𝟙 deed`. the runner performeþ that deed; see [deeds](#deeds).

declarations are private by default. `show` publisheþ a declaration.
`show ilk` publisheþ þe family and its constructors; its eliminator
followþ þe family. `show
name` re-exporteþ the visible declaration spelled `name`; `show ns~name`
publisheþ it as `name`. ordinary `use` doth not re-export anything.

lets, ilks, constructors, flocks, and flock members share one namespace. a
module declareþ each top-level name once, so a flock and its member, or an
ilk and its constructor, need different names; bookhoard prefixeþ such a
flock wiþ `haþ_` and such a type wiþ `_`.

## libraries and imports

`use path` importeþ a module. its final path segment, up to þe first dot,
becomeþ the default namespace. an optional final name replaceþ it.

```tung
use ilk/list.tung
use ilk/table.tung hashmap

let xs ≔ list~empty
let entries ≔ hashmap~empty
```

visible imported names may remain bare when unambiguous. two different direct
imports cannot claim the same namespace. the import graph must be acyclic. a
local term shadoweþ an imported bare term in value and application positions. a
qualified name still reacheþ the import.

re-exported names retain their defining identities. ambiguous bare names
must be qualified wiþ a direct import namespace; diagnostics suggest þose
visible namespaces. a missing or cyclic use is reported at its importing
statement, in þe module containing þat statement.

cached modules must agree on every shared defining identity, including
transitive dependencies. different definitions of one identity are rejected
at þe incoming `use`; an identical dependency reached along two paths is
accepted.

the host catalogue explicitly overloadeþ primitive names, such as `+` for
integer and float, within primitive scope. direct application trieþ their
signatures in catalogue order. as a value, the name selecteþ þe first signature.
a local value shadoweþ an imported constructor of the same spelling, in
patterns too: þere the name bindeþ a variable, and a qualified name still
reacheþ the constructor.

module lookup searcheþ paths relative to the importing file, declared library roots,
þen `TUNG_PATH` entries. a `.tung` path resolving to different files is
ambiguous. `ground.tung` is an optional import, not a prelude.

### manifests

the standard library is an ordinary library in [`bookhoard/`](../bookhoard/).
a `tung.yaml` manifest declareþ local library paths or pinned git repositories
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

each dependency key nameþ one library throughout the graph, not a local alias.
`path` giveþ a live directory relative to the declaring manifest, or an
absolute directory. it need not be a git repository. changes there take effect
without a commit. `repo` giveþ a git URL or local git repository path, such as
`../my-library`. `hash` giveþ its full 40- or 64-digit hexadecimal commit hash.
quote a hash so yaml readeþ an all-digit value as text. specify either `path`
or both `repo` and `hash`. an optional `subdir` selecteþ a library inside the
pinned checkout. it must stay inside that checkout, even through symlinks.
omit `subdir` when the repository root is the library. external projects may
pin Bookhoard with `repo: https://github.com/jukisima/tung.git`, a published
commit hash, and `subdir: bookhoard`. `use` paths name `.tung` files relative to
the selected library root.

tung findeþ the nearest `tung.yaml` above the source file. local paths are
resolved from the manifest that declareþ them. git pins are checked out under
`.tung/libraries/` beside the root manifest. after the first fetch, tung
reuseþ the checkout offline. `tung --library-paths [project-path]` listeþ the
resolved roots. `TUNG_PATH` addeth roots outside manifest resolution.

each library may declare `tung.yaml`. tung traverseþ the whole dependency graph,
including libraries the program doth not import. matching git pins share one
checkout; matching local paths share one root. before module checking, tung
rejecteþ:

- one name with different sources, including a path and a git pin;
- one repository locator and subdirectory with different names or commits;
- one local path with different names.

if two libraries pin `shared` to different commits, the project faileþ. the
root manifest cannot override either pin. two names for one repository also
conflict when they select the same subdirectory, even at the same commit.
different subdirectories of one repository may supply distinct libraries.

relative git repository paths resolve from the manifest that declareþ them and
are lexically normalised. local library paths are canonicalised, so aliases to
one directory count as one path. remote locators are compared as written.
`subdir` is normalised and cannot contain `..`. use the same name and source in
every manifest. `TUNG_PATH` roots lie outside manifest conflict checking. the
same `.tung` path in different roots remaineþ ambiguous when imported.

## nonstandard keywords

tung nameþ several features wiþ anglish words. each word below is a keyword
or a contextual word wiþ þe meaning of þe general term.

| tung       | general term     | use                                       |
| ---------- | ---------------- | ----------------------------------------- |
| `ilk`      | data type        | `ilk name: kind { constructors }`         |
| `flock`    | type class       | `flock name: [parameters, *] { members }` |
| `bizen`    | instance         | `bizen: type { definitions }`             |
| `fallback` | default instance | `bizen fallback: type { … }`              |
| `deed`     | io action        | `α deed`                                  |
| `fremmed`  | foreign binding  | `let name: type ≔ 'key' fremmed`          |
| `orsend`   | axiom            | `orsend name: type`                       |
| `fall`     | function         | `fall inputs, result ^ body`              |
| `unbuild`  | eliminator       | `motive unbuild name methods value`       |
| `show`     | export           | `show let …`, `show a, b`                 |
| `use`      | import           | `use path.tung alias`                     |
| `yield`    | block result     | `(let … yield result)`                    |

þe project's own names follow þe same direction: `tongue` is þe compiler,
`bookhoard` þe standard library, and `byspel` þe examples.

## names, comments, and literals

most non-space, non-reserved characters may occur in names. `~` qualifieþ
imports; `.` selecteþ record fields; `^` separateþ a match case's patterns from its
result. type alias, data, and flock names are unqualified. so are þeir
constructors and members. outside `.tung` import paths, a name may contain at
most one `~`. its namespace and member must be nonempty and slash-free. `‥` is
an ordinary name; there is no general infix escape. `_` discardeþ a binding or
match value.

names, keywords, host keys, and `.tung` paths use snake_case: words are
lowercase and joined by `_`, as in `to_text`, `map_flat`, and
`flock/order/less_equal.tung`. `-` remaineþ a legal name character, so this is
a convention, not a lexical rule.

`#` starteþ a line comment. `/* ... */` formeþ a non-nested block comment. `##`
and `/** ... */` attach doc comments to the next declaration. editor help and
generated bookhoard pages use them.

an integer literal of type `ℤ` always hath a sign: `+42`, `-7`, `+0`. unsigned
digits such as `42` are a natural number of type `ℕ`. boþ are arbitrary
precision; the compiler storeþ naturals as haskell `Natural`. `+ 1` wiþ a space
is the name `+` applied to the natural `1`. `ℕ` subtraction stoppeþ at zero:
`2 - 3` is `0`. a quantity þat cannot be negative is a `ℕ`: counts, indices,
durations in milliseconds, ports, exit codes, http status codes, and unicode
code points. float literals contain a decimal point and an optional `-`. a
backtick introduceþ one unicode scalar, and single quotes delimit text. both literal forms accept `\n`, `\r`, `\t`, `\'`, `\\`, and
decimal escapes such as `\23383;`.

## application

every function is curried. in an unmarked sequence of two or more terms, the
second is the function. the others are arguments in order.

```tung
a f           # f a
a f b c       # f a b c
a f $ g b     # g (f a) b
```

`$` groupeþ its left expression and useþ the next atom as the function. `$(`
starteþ a function-first segment.

`<{f, a, b, c}` lowereþ to `(a f b) f c`. `>{f, a, b, c}` lowereþ to
`a f (b f c)`. each requireþ a combining function and at least two values. `r{`,
`<{`, and `>{` are single opening delimiters. the brace must touch the
marker.

runtime evaluation is call-by-need. application arguments, local `let`
values, globals, record fields, and constructor fields are computed when
inspected and shared thereafter. unused values are not computed. `match`
inspecteþ its scrutinee and computeþ only its selected branch; recursive
hypotheses follow þe same rule. a failure value, such as `sorry`, faileþ
when inspected. pure native operations compute their inputs fully. host
deed inputs and deed results are computed fully when þe deed is performed.
building a deed performeþ no action.

## declarations and types

`ilk name:signature {constructors}` declareþ a data type. the signature is `*`
for a type wiþout parameters, or a bracket of kinded parameters ending in `*`,
as in `[a: *, *]`. `*` is a universe with an inferred level. `[*, *]` is a function type from
types to types. only a standalone `*` is universe syntax. names such as `‥` remain
ordinary names. the magma operation is `·`.

constructors are comma-separated, and every constructor stateþ its type, as in
a GADT: `name:type`. a bracketed type listeþ optional `@` parameters, þe
field types, and þe result type; a single type is þe result alone, as in
`none: a option`. fields are bare types, as in `some: [a, a option]`. the
result type must name the declared `ilk` with its full arity. a constructor wiþout a type is an error.

```tung
ilk list: [a: *, *] {
  empty: a list,
  ‥: [a, a list, a list]
}
```

constructors may choose different result indices. a match refineþ each index
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

`fall slots, result ^ body` writeþ a typed function as an expression. its
items are product slots; þe last is þe result type, `^` followeþ, and þe
body extendeþ to þe end of þe expression. a bare slot bindeþ no name, and
`fall` requireþ at least one input, so `fall * ^ *` is rejected.

```tung
let sameness ≔ fall @α: *, a: α, α ^ a
let powerset ≔ fall α: *, * ^ [α, *]
```

`let name ≔ body` bindeþ a name. `let name:annotation ≔ body` also annotateþ
it. the header is only the name; arguments are named slots of the annotation.
a slot wiþ no type after its `:` is inferred from þe body, so
`let add: [x:, y: ℤ, ℤ] ≔ x + y` inferþ `x: ℤ`. `_` is never a type; it only
discardeþ an input. a let's type must be fully determined: a let is never
generalised over unknown types, so a polymorphic let writeþ its parameters,
as `let identity: [@α: *, x: α, α] ≔ x`.

```tung
let count ≔ 42
let answer: ℤ ≔ +42
let identity: [x:] ≔ x
let identity: [@a: *, x: a, a] ≔ x
let identity: [@a: *, a, a] ≔ {x ^ x}
let add_after: [x:, y: ℤ, ℤ] ≔ x + y
```

an annotation is one type or a bracketed list of slots:

- one type annotateþ a value.
- a bracket list holdeþ `@name:kind` type parameters and `@:flock`
  requirements, then value slots, as described below.
- a bracket wiþ one bare expression is þat expression; without an input it
  introduceþ no function argument.
- `pattern:type` is a named slot. it bindeþ an argument for the body. its
  pattern followeþ the second-is-function rule and needeþ no grouping, as in
  `let unbox:[@a:*, x box:a box, a] ≔ x` and `a boþ b`. a slot named by a
  constructor wiþout fields matcheþ þat constructor, so
  `let symmetry:[@α:*, @a:α, @b:α, reflect:a = b, b = a] ≔ reflect` rewriteþ
  `b` to `a` in þe result. þe match itself is þe evidence: `_:a = b` doth
  not inspect þe proof, so `b` stayeþ distinct from `a`. slot patterns never match literals; use `match`.
- a bare slot giveþ a type only and bindeth no name. the body supplieþ bare
  arguments, usually wiþ an anonymous function. named slots precede bare
  slots.
- the final bare slot is the result type. after a named slot, omit it to
  infer the result.
- `_:type` as a slot discardeþ an argument.
- the formatter writeþ `:` wiþ no space before and one space after: `x: α`.
- an annotation must be followed by `≔`.

an annotation endeþ in a kind declareþ a type alias; see
[type expressions](#type-expressions).

use Greek letters for generic polymorphic parameters. type and flock names
carry no `*` prefix, and no term reuseþ a type's name: name a slot `l`, not
`list`, beside `list`. when a constructor would share its type's name, the
constructor getteþ a new name (`boþ` wiþ `boþ`, `complex` wiþ `+i`, `nonempty`
wiþ `‥′`), or, for a type wiþ one constructor, the type takeþ a `_` prefix
(`_request` wiþ `request`). a flock whose member would share its name takeþ a
`haþ_` prefix (`haþ_zero` wiþ `zero`). `*name` still lexeþ as one name, and
standalone `*` is syntax.

leading `@name:kind` declareþ a polymorphic type parameter. use `@a:*` for
an ordinary type and `@f:[*, *]` for a unary type constructor.
type declarations use `name:kind` wiþout `@`.
every type variable in a written annotation must be declared or already in
scope, including type constructor variables. a
requirement nameþ only parameters declared before it.
unknown names are errors. an unannotated `let identity: [x:] ≔ x` may still infer
a polymorphic type.

an anonymous function bound by `let` may call itself, with or without an
annotation. other initialisers see preceding bindings, including a preceding
binding with the same name. an unguarded self-reference is an error.

data, alias, and flock parameters scope over þeir declarations.
flock methods, constructors, and laws may introduce local leading `@` parameters.
local parameters cannot redeclare þeir owner parameters.
an instance's type listeþ its variables and requirements before its head:
`bizen:[@a:*, @:a equal, (a list) equal] {...}`.
these variables scope over its head, requirements, and members. a constructor such as
`pack [@a:*, a, packed]` declareþ an existential payload when matched.

calls may supply declared implicit parameters explicitly, including values. `@text` passeþ a named
type; `@(text list)` passeþ a compound type. type arguments select header
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
with `@a`. explicit type input requireþ a declared header parameter or a value
wiþ an explicitly quantified type.

inside a function type, leading `@name:kind` bindeth an explicit universal
quantifier. its scope is that bracketed type. quantifiers may occur in arguments
or results, at any rank:

```tung
let both: [f: [@a: *, a, a], r{number: ℤ, word: text}] ≔
  r{number≔+1 f, word≔'x' f}
let make: [_: ℤ, [@a: *, a, a]] ≔ {x ^ x}
```

`both` requireþ a function that workeþ for every `a`. each use of `f`
instantiateþ it independently. `make` returneþ such a function. a monomorphic
function cannot satisfy either quantified type. nested binders shadow outer
type variables; other free variables retain their outer meaning.

higher-rank types require explicit annotations. universe constraints enforce
predicativity; inferred type inputs may themselves be function types. passing an anonymous function checkeþ its arguments against the expected
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

type application useþ second-is-function syntax.
`ℤ list` applieþ `list` to `ℤ`; `a boþ b` applieþ the binary product type.
a let returning `*` defineþ a transparent type function, as in
`let powerset:[a:*, *] ≔ a → 𝟚`. `let count:* ≔ ℤ` defineþ a transparent
constant. types and values use one expression syntax. type functions may take
value inputs and requirements; partial application followeþ ordinary function
application. conversion unfoldeth transparent definitions.

function types use `[argument, result]`. nested brackets describe function
arguments. `→` is an ordinary name, not syntax. `combinator.tung` defineþ it,
and `ground.tung` showeþ it:

```tung
show let →: [α: *, β: *, *] ≔ [α, β]
```

`a → b` is ordinary type application, so it hath no associativity: write
`a → (b → c)`. because its body applieþ the function type constructor to its
parameters, `→` may be passed unapplied to a flock, as in
`bizen: → semigroupoid`. `(term:type)` constraineþ any term.

```tung
let powerset: [a: *, *] ≔ a → 𝟚
let call: [@a: *, @b: *, f: [a, b], x: a, b] ≔ x f
let answer ≔ (+1 + +2: ℤ)
```

a local alias of a function parameter retaineþ its type constraints.

a let whose body nameþ itself is recursive, unless a binding of that name is
already visible, such as an import or an outer local; then the mention refereþ
to that binding, so `use source.tung let value ≔ value + +1` extendeþ the
import. a recursive let needeþ an annotation, or an ascribed body such as
`let f ≔ (body: [ℕ, ℕ])`. recursion must be structural; see
[dependent.md](dependent.md#pattern-matching-and-recursion).

### composition and lists

`<{f, a, b, c}` and `>{f, a, b, c}` work in type expressions as well as
terms. they expand to `(a f b) f c` and `a f (b f c)`, respectively.
composition hath no special list rules. native type-list kinds and operators
have been removed. the compiler useþ one ordinary list family for
values, types, and type constructors. see
[dependent lists](dependent.md#ordinary-lists) for checked examples and indices.

## algebraic data and patterns

`ilk` declareþ an algebraic data type. type parameters and constructor arguments
follow the ordinary sequence rule.

```tung
ilk option: [a: *, *] {
  none: a option,
  some: [a, a option]
}
```

constructor application is curried. patterns may bind variables, use `_`, match
exact natural, integer, or text literals, or destructure constructors. `n succeed`
matcheþ a positive natural and bindeþ its predecessor, so `0` and `n succeed`
together cover `ℕ`, and a function on `ℕ` may recurse on `n`. as a term,
`succeed: [ℕ, ℕ]` addeþ one, unless a constructor named `succeed` is in scope.
each binder may occur only once in a pattern row.

`match` consumeþ one or more comma-separated scrutinees. `{...}` formeþ an
anonymous function with one curried input per pattern. `^` separateþ a case from
its result. `;` joineþ complete alternative rows that share a result. when a
scrutinee is a computation, such as `a ≤ a`, each row's expected type hath
that row's constructor in its place, so `match a ≤ a {yea ^ reflect, nay ^
reflect}` proveþ a statement about `a ≤ a` by cases. the
[dependent rules](dependent.md#inductive-declarations-and-proofs) give the
exact conditions.

`match e for known { rows }` nameþ þe equation between one scrutinee and
each pattern. in a row whose pattern is `p`, `known` haþ type `e = p`, so a
branch can use what þe match learned about a computed scrutinee. it matcheþ
a fresh copy of `e`, as lean's `match h : e wiþ` doþ, so `e` itself is not
refined in place. `for` endeþ þe scrutinee only in a match header; elsewhere
it is an ordinary name. a match wiþ more þan one scrutinee cannot name an
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

the checker rejecteþ non-exhaustive and redundant rows over algebraic data.
finite rows of integer or text literals need a variable or `_`, as þese types
have infinitely many values. natural rows may instead end wiþ `n succeed`. an empty function `{}` eliminateþ an annotated
uninhabited input such as `𝟘`.

`unbuild name` is þe eliminator of þe ilk or flock `name`, as a term. it takeþ
a motive, one method per constructor, and þe value, so a proof by
structural induction is written wiþ þe motive first:

```tung
let doubled: [l: ℕ list, ℕ list] ≔
  {_: ℕ list ^ ℕ list} unbuild list empty {first, _, rest ^ first ‥ (first ‥ rest)} l
```

`name` may be qualified, and `unbuild ℕ` and `unbuild =` name þe primitive
eliminators. any name þat is not an ilk or flock is rejected. þe
[dependent rules](dependent.md#inductive-declarations-and-proofs) define þe
method types.

## records

records are closed. `r{field:type}` formeþ a type; `r{field ≔ value}` formeþ a
value. an update placeþ its base after `≔`. later entries set or remove fields.

```tung
let person: r{name: text, age: ℤ} ≔
  r{name ≔ 'naoki', age ≔ +35}
let older ≔ r{≔ person, age ≔ +36}
let public ≔ r{≔ person, - age}
let age ≔ older.age
```

in `record.field`, `record` is a term and `field` an unqualified field name.
access chaineþ leftward: `record.outer.inner` selecteþ `outer`, then `inner`.
field sets must match an annotated record type. duplicate labels, unknown field
removal, and non-record updates are errors.

## flocks, bizens, and laws

þe [keyword table](#nonstandard-keywords) giveþ þe general terms for
`flock` and `bizen`.

`flock name:[parameters, @:parent, *] {...}` declareþ a flock. its signature
listeþ `name:kind` parameters and `@:parent` requirements and endeþ in `*`;
`flock name:* {...}` hath no parameters. `a:*` declareþ a type parameter.
`f:[*, *]` declareþ a unary type constructor parameter.

`bizen:head {...}` provideþ evidence and member implementations. the head keepeþ
second-is-function order: `bizen:ℤ convert text {...}`. a bizen wiþ
parameters or requirements writeþ þem before the head in one bracket:
`bizen:[@a:*, @:a equal, (a list) equal] {...}`.

`@:a equal` in a header stateþ required evidence. requirements and `@`
parameters precede value arguments, in any order among þemselves, but a
requirement nameþ only parameters declared before it. flock and bizen headers
have no value arguments. a required member is `let name:type` wiþ no body; a
function member writeþ its inputs and result in brackets. a law is a named
member whose type is an equality on terms: `let name:[binders, left = right]`
bindeþ typed patterns and endeþ in its equation. a law hath no body.

```tung
flock equal: [a: *, *] {
  let ≍: [a, a, 𝟚]
  let reflexive: [x: a, (x ≍ x) = yea]
}

let ≭: [@a: *, @: a equal, a: a, b: a, 𝟚] ≔ (a ≍ b) if nay yea

flock applicative: [f: [*, *], @: f functor, *] {...}
bizen: [@b: *, @: b ring, @a: *, [a, b] ring] {...}

bizen: 𝟚 equal {
  let ≍ ≔ {
    yea, yea ^ yea,
    nay, nay ^ yea,
    _, _ ^ nay
  }
  let reflexive ≔ sorry
}
```

`=` is the [identity type](#equality) in scope, applied under the
second-is-function rule: each side is one term, so a compound side needeþ parentheses, as in
`(a ∧ a) = a`. law brackets require a type for each pattern. a law name shareþ the flock's member
namespace, so it cannot repeat a member or anoþer law. `let` implementations inside `bizen`
use ordinary declaration syntax.

a bizen must supply each required member not supplied by a parent. a child bizen
also witnesseþ required parent flocks and may define inherited members.
duplicate bizens are incoherent.
an annotated member must satisfy its own signature and the required method type. a member þat nameþ
itself refereþ to þe flock, found by instance search; þe bizen is not yet
registered while its members are checked, so a recursive member is a
recursive let þat þe member nameþ, as `let ∋ ≔ list_holds` in
`ilk/list.tung`.

selection useþ local requirements, registered bizens, then inherited
instances, as lean doþ. registered bizens are tried by priority, higher
first, and þe latest declared first among equals; þe first þat matcheþ,
wiþ its own requirements, is chosen. `bizen 10: …` writeþ a priority; þe
default is 1000. inherited search useþ the first matching path.

a flock parameter written `β: * out` is an output: search findeþ it, as
lean's `outParam` doþ. a goal waiteþ while þe head of an input parameter is
unknown. a goal still stuck on an unknown input trieþ þe flock's fallback
bizens, written `bizen fallback: …`, as lean's default instances; for
example þe function `category` bizen is a fallback, so `sameness` used as a
function findeþ it. wiþout a fallback, þe goal needeþ an annotation or
stayeþ unsolved, and þe let needeþ an annotation.
[dependent instance search](dependent.md#flocks-and-bizens) defineþ cycles,
depth, waiting goals, and candidate requirements.

## equality

`x = y` is the type of proofs that `x` and `y` are equal; both sides share one
type. `=` and `reflect` are primitive and visible in every module, like `ℕ`.
bookhoard's `equality.tung` proveþ þe lemmas `leibnitz`, `symmetry`,
`transitivity`, and `transport`.

its only constructor is `reflect: [@α: *, @x: α, x = x]`, so `reflect`
proveþ any equation that holdeþ by computation. a proof of `x = y` may be
matched against `reflect`, which rewriteþ `y` to `x` in that branch. when
boþ sides are built from constructors, matching compareþ þem: matching
constructors equate þeir fields, so `reflect: (a ‥ l) = (b ‥ m)` giveþ
`a = b`, and different constructors make þe match empty, so
`[yea = nay, 𝟘] ≔ {}` holdeþ. `≍` is
boolean equality, a flock member that computeþ `yea` or `nay`; `≔` defineþ a
name and is not an equation.

```tung
let one: ℕ ≔ 1
let checked: one = 1 ≔ reflect
let symmetric: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔
  match p { reflect ^ reflect }
```

a law statement is a type over the flock's members. each bizen proveþ every
law of its flock, and also þe laws of each parent flock it witnesseþ because
þat parent hath no bizen of its own. a proof is checked against the law with
this bizen's own members, so a law about `≍` is stated for the bizen's `≍`:

```tung
bizen: 𝟚 equal {
  let ≍ ≔ ...
  let reflexive ≔ {x ^ ...}
}
```

a law is an ordinary member whose type is an equation. a missing law is an
error, and `sorry` assumeþ one. þe compiler neiþer executeþ nor rewriteþ
wiþ laws. a law name is a top-level accessor like any member name, so
`rule @α x` is a proof term, and a flock requirement carrieþ its laws: a
proof may use a required dictionary's laws as evidence. two flocks cannot
share a law name.

`sorry` is a term of any type. it standeþ for an omitted proof or definition.
inspecting it is a runtime error. an uninspected `sorry` never faileþ, even
as a top-level `let`. it is an unchecked assumption, not a proof. the
[logical boundary](dependent.md#logical-boundary) defineþ this limitation.

`orsend name: type` declareþ a named assumption: a constant of þat type
wiþout a proof. it is top-level and may be shown; its annotation must be a
type and may not bind inputs. checking never unfoldeþ it, and reaching it at
run time faileþ wiþ `reached orsend 'name'`. an `orsend` is a deliberate,
listed assumption, such as an axiom a proof relieþ on; `sorry` remaineþ an
unfinished hole.

each `sorry` is also a hole. checking recordeþ its goal, þe type expected
þere, and its named context, þe locals in scope wiþ þeir types, outermost
first. a pattern variable showeþ under its own name. `--check` printeþ each
goal after þe `sorry` lines as `path:line:column:line:column: goal: type`,
followed by one indented `name: type` line per local, and þe editor showeþ
þe same text as information at þe hole and in hover. a goal keepeþ each definition
by name unless unfolding it reacheþ a constructor, literal, record, or
variable, and a recursive call keepeþ its name, so a goal readeþ
`(first ‥ (rest · (b · c))) = (first ‥ ((rest · b) · c))`.

## deeds

`α deed` is an action þat yieldeþ an `α` when performed, like haskell `IO` or
purescript `Effect`. `deed` is a primitive type constructor of kind `[*, *]`.
it is a reserved keyword for editors and metadata but lexeþ as an ordinary
name, so `α deed` is type application.

evaluation never performeþ a deed. building, storing, passing, or combining
deeds performeþ noþing. performing a deed computeþ values fully: a host deed's
inputs are computed fully before þe host acteþ, and þe result of each
performed deed is computed fully before þe next step receiveþ it. fully
computed meaneþ every constructor field, record field, and literal is
computed; functions and deeds inside þe value stay as þey are. so
`let main: 𝟙 deed ≔ 40 fibonacci $ to_text $ write_line` computeþ the number
when `main` writeþ it, and an accumulator passed between þe steps of a
`deed_fix` loop doth not build a chain of pending work. the runner performeþ
`main`. interactive evaluation performeþ a deed only when it is the final
`yield`, as a repl prompt doth; a yielded value is computed fully before it
printeþ.

deeds compose only through bookhoard's monad methods; þere is no sequencing
syntax. `deed/action.tung` provideþ `deed functor`, `deed applicative`, and
`deed monad`, built on the host bindings `deed_pure` and `deed_bind`:

- `pure` wrappeþ a value in a deed þat performeþ noþing;
- `map` changeþ a deed's result;
- `map_flat` passeþ a deed's result to the function þat chooseþ the next deed;
- `þen` performeþ two deeds in order and keepeþ the second result;
- `>{þen, a, b, c}` performeþ several deeds in order;
- `lift₂` and `apply` perform their deeds from left to right;
- `each` performeþ an action for each list element in order;
- `deed_fix` repeateþ a deed: its step receiveþ the repeated deed itself, so
  `{again ^ read deed_bind {none ^ only deed_pure, _ some ^ again}} deed_fix`
  readeþ until input endeþ.

```tung
let greet: [name: text, 𝟙 deed] ≔ ('hello, ' write) þen (name write_line)

let main: 𝟙 deed ≔ read map_flat {
  line some ^ line greet,
  none ^ 'no input' write_line
}
```

noþing throweþ. a fallible operation returneþ a value. `option` is used when
absence explaineþ the failure. `text ∑ α` is used when a message doth:
`inject₀` carrieþ the message and `inject₁` the result.

- `%`, `from_text`, `to_ℕ`, `natural_to_unicode`, `⌊` of a non-finite float,
  and list `at` return `option`;
- `read` yieldeþ none at the end of input;
- `read_file`, `write_file`, `append_file`, and `run_process` yield `∑`;
- `environment` yieldeþ none for an unset variable;
- `wait` yieldeþ none for a cancelled task, and `wait_for` also yieldeþ none
  after its timeout;
- `serve` yieldeþ a message when the server stopeþ.

## runtime boundary

`main` must have type `𝟙 deed`. the checker rejecteþ any other type, including
a function from `𝟙`. the runner performeþ `main` once and leaveþ unused
top-level definitions unevaluated. it printeþ noþing of its own on success; a parse, type, or runtime
error is printed and the exit status is 1. `tung file.tung args…` passeþ the
trailing arguments to `arguments`. `exit` endeþ the whole run wiþ its status;
inside a task it endeþ only that task, which þen hath no result.

`--check`, `--check-module`, and `--check-stdin` return status 0 only after
successful checking. a rejected source returneþ status 1. after `type ok`,
each line `sorry: name` nameþ a shown declaration, bizen, or `main` of þe
checked file whose body useþ `sorry`, directly or þrough any definition it
useþ. a bizen whose law is `sorry` is listed as `sorry: bizen type`. a host binding is a program, not an assumption.
`--no-sorry` before þe command turneþ any such assumption into a failure:
þe lines are printed and þe status is 1. it also refuseþ to run a program
whose `main` assumeþ `sorry`. each line `orsend: name: type` þen nameþ an
`orsend` declared in þe checked file; `--no-sorry` allowþ þem. þe goal of
each `sorry` followeþ, as described under [`sorry`](#equality).

an annotated file-level `let` may bind a host operation. a text key precedeþ
`fremmed`. the host key and full declared type must match the compiler
catalogue. a host binding wiþout arguments must have a deed type; performing
the deed runneþ the host action. `_foreign.tung` and the `deed/` modules
declare the runner's deeds: console text, `random`, tasks, `sleep`, files,
arguments, environment, `exit`, the clock, processes, the web server, and
`deed_fix`. every pure host operation hath one definition, shared by the
erased evaluator and normalising kernel.

a pure host operation may name a model after `fremmed`:
`let add_natural: [ℕ, ℕ, ℕ] ≔ 'add_natural' fremmed add_natural_model`. þe
model is an ordinary let of þe same type. checking computeþ natively when
every input is a literal and unfoldeþ þe model oþerwise, so a proof can
reason about þe operation, as `[n: ℕ, (n + 0) = n] ≔ reflect`; þe runner
always useþ þe native operation. a deed operation cannot have a model.
`ilk/natural.tung` modelþ `ℕ` equality, order, addition, subtraction, and
multiplication.

the compiler provideþ no operation or bizen by itself. `ℕ`, `ℤ`, `float`,
`unicode`, and `text` are primitive types, but every operation on þem,
including `+` and `≍`, is a `fremmed` binding wrapped by a bookhoard bizen;
`ilk/natural.tung`, `ilk/integer.tung`, and `ilk/float.tung` declare þe
numeric ones. a program þat useþ arithmetic þerefore importeþ bookhoard,
usually þrough `ground.tung`.

`deed` and `task` are opaque primitive families of kind `[*, *]`. only the
runner startþ a task. they have no data constructor or eliminator;
`fork`, `wait`, `wait_for`, and `cancel` are their operations.

a host data type, such as `option`, `list`, or `𝟙`, is þe `ilk` of its name
declared in its bookhoard file, such as `ilk/option.tung`. an `ilk` of þe same
name elsewhere is a different type, whatever its constructors.
the required constructor and field schemas are described under
[dependent host bindings](dependent.md#deeds-and-host-bindings).

the
[bookhoard reference guide](../bookhoard/reference.md)
explaineþ the standard library's design boundaries. runnable examples live under
[`byspel/`](../byspel/).
