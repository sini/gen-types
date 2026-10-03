# gen-types — clean-room structural type checker for the pure-gen ecosystem

[![CI](https://github.com/sini/gen-types/actions/workflows/ci.yml/badge.svg)](https://github.com/sini/gen-types/actions/workflows/ci.yml) [![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-pink?logo=github)](https://github.com/sponsors/sini)

A pure, `nixpkgs.lib`-free **structural type checker** for Nix — the *checking half*
of a pure-Nix module system.

A type is a predicate boundary: `verify` a value and get back `null` (it inhabits the
type) or an error string (it does not). Nothing else. gen-types owns no merging, no
priorities, no fixpoint — a downstream byte-mode **merge engine** (`gen-merge`) sits
above it and calls these checkers to verify leaves. That split is deliberate: gen-types
is a self-contained **leaf** library so it can be imported *below* a registry like
`gen-schema` without a flake cycle.

- **Pure.** No `nixpkgs.lib`, no `evalModules`, no `mkOption`. `builtins` plus the
  handful of utilities in [gen-prelude](https://github.com/sini/gen-prelude) — its only
  dependency. The [purity invariant](./ci/tests/types-purity.nix) is a CI-checked
  property with teeth.
- **Frugal.** A successful `verify` is a single evaluation pass; on failure it re-scans
  only to locate the first offending element. Structs allocate no intermediate attrset
  on the happy path.

## Gen Ecosystem

| Library                                              | Role                                                                                                                   |
| ---------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------- |
| [gen-prelude](https://github.com/sini/gen-prelude)   | Pure nixpkgs-lib-free utility base (builtins re-exports + vendored lib utils)                                          |
| [gen-algebra](https://github.com/sini/gen-algebra)   | Pure primitives (record, either, intensional identity)                                                                 |
| [gen-types](https://github.com/sini/gen-types)       | **This lib** — Clean-room MIT structural type checker (leaf/poly checkers; `verify: v → null\|err`)                    |
| [gen-merge](https://github.com/sini/gen-merge)       | Byte-mode module merge engine (`evalModuleTree`, byte-identical to nixpkgs `lib.evalModules` over the priority subset) |
| [gen-schema](https://github.com/sini/gen-schema)     | Typed registries (kinds, instances, collections, refs); re-hosted on gen-merge                                         |
| [gen-aspects](https://github.com/sini/gen-aspects)   | Aspect type system (traits, classification, dispatch); re-hosted on gen-merge                                          |
| [gen-scope](https://github.com/sini/gen-scope)       | HOAG scope-graph evaluator (demand-driven, \_eval memoization, circular attributes)                                    |
| [gen-graph](https://github.com/sini/gen-graph)       | Accessor-based graph query combinators (traversal, condensation, phaseOrder)                                           |
| [gen-select](https://github.com/sini/gen-select)     | Selector algebra (pattern matching over graph positions)                                                               |
| [gen-bind](https://github.com/sini/gen-bind)         | Module binding (inject external args into NixOS modules)                                                               |
| [gen-dispatch](https://github.com/sini/gen-dispatch) | Relational rule dispatch STEP (stratified phases, conflict resolution)                                                 |
| [gen-memo](https://github.com/sini/gen-memo)         | The incremental plane — decides reuse, never evaluates (change propagation, AFFECTED set)                              |
| [gen-vars](https://github.com/sini/gen-vars)         | Pure-Nix vars/secrets (den-agnostic)                                                                                   |

## Install

```nix
# flake.nix
{
  inputs.gen-types.url = "github:sini/gen-types";
  outputs = { gen-types, ... }: {
    # gen-types.lib is the checker set
  };
}
```

Or plain import (fetches the flake-locked gen-prelude by default):

```nix
let t = import (builtins.fetchGit "https://github.com/sini/gen-types") { };
in t.int.verify 5   # => null
```

## The checker value

Every constructor returns a record:

```nix
{
  name;    # full structural name, e.g. "listOf<int>", within 256 bytes (see below)
  verify;  # value -> null | errString      (null = ok)
  check;   # v: v2: throws verify's error on failure, else returns v2
  __name;  # base name with polymorphic metadata stripped ("listOf")
  __nameWithin;  # budget -> the name within that many bytes; a combinator reads a member through it
  __mint;  # tagged identity regime: { minted = "type:<sha256>"; } | { unmintable = { ctor; reason; }; }
  __id;    # the accessor for a consumer DEMANDING an identity: the minted value, or a named refusal (lazy)
  __payload;  # the mint's preimage, read-only, NOT identity: { minted = { ctor; args; }; } | { unmintable = { ctor; }; }
  __okAt;  # composites only: the step-indexed guard bounding type nesting for the mint (see below)
}
```

```nix
t.int.verify 5              # => null
t.int.verify "x"            # => "expected type 'int' but value \"x\" is of type 'string'"
t.int.check 5 5             # => 5        (validate-and-pass-through)
t.int.check "x" "x"         # => throws the error above
```

## API

### Primitives

`string` / `str`, `int`, `bool`, `float`, `number`, `path`, `pathLike`, `attrs`,
`list`, `function`, `derivation`, `null`, `any`, `never`.

### Polymorphic combinators

```nix
t.option t.int                       # null, or an int
t.listOf t.str                       # list of strings
t.attrsOf t.int                      # attrset of ints
t.union [ t.int t.str ]              # int or string
t.intersection [ t.int t.number ]    # int and number
t.enum "color" [ "red" "green" ]     # membership
t.tuple [ t.int t.str ]              # positional [int, string]
t.optionalAttr t.int                 # an int; struct treats the key as omittable
```

A combinator's members must be checkers. A member with no `verify` (a gen-merge merge
strategy such as `submodule`, which carries `admits` instead) is refused by name and
catchably, when the combinator is first used, whatever the value and whatever the member
order:

```nix
(t.union [ t.str submodule ]).verify "hello"
# => throws "gen-types: union: member 'submodule' is not a checker (it carries no `verify`); …"
```

The check reaches the combinator that directly holds the member. It runs at use rather
than when the combinator is applied, because a self-referential type
(`let r = t.union [ t.int (t.listOf r) ]; in r`) would otherwise diverge. So a
non-checker nested one level further in is found only when the outer combinator reaches
it, and these ill-formed types still answer `null`:
`t.listOf (t.union [ t.str m ])` given `[ ]`, `t.option (t.union [ t.str m ])` given
`null`, and a struct key declared `t.optionalAttr m` when the key is absent.

Errors thread context through nesting:

```nix
(t.attrsOf (t.listOf t.int)).verify { a = [ 1 "x" ]; }
# => "in attrsOf<listOf<int>> value: in listOf<int> element:
#     expected type 'int' but value \"x\" is of type 'string'"
```

A refusal renders the offending value **shallowly**: it reads the value and never a member of
it, so a member that throws, errors, cycles or nests cannot abort or replace the refusal. A list
shows its length, a set its attribute names, and a member's value is `…`:

```nix
t.int.verify [ 1 2 ]         # => "expected type 'int' but value [ … (2 elements) ] is of type 'list'"
t.int.verify { a = 1 + "a"; } # => "expected type 'int' but value { a = …; } is of type 'set'"
```

The rendered value is bounded by a 256-byte budget: a string or path is cut with a trailing
`…`, and a set's names fill the budget and count the rest as `… (N more)`. It stays within
290 bytes, except a top-level float, whose `toString` is bounded by its representation
(`1.5e300` renders 308 B). The bound covers this value slot only: `struct`'s closed-world
refusal and `strict` list unknown key names in full.

The type's name in the same refusal is bounded by the same 256 bytes. A combinator renders
its name within the budget and hands each member a strictly smaller one, so the name of a
self-referential type is finite and its refusal returns. `let r = t.union [ t.int (t.listOf r) ]; in r.verify "a"` names the type in 250 bytes: `union<int,listOf<` 13 times, then `…` and the
closing brackets. Past the budget, the remaining members collapse into `…`. A name of
at most 256 − 3d bytes (d its nesting depth, so 253 when flat) is unchanged. This covers every
name a gen-types combinator builds; a hand-built member whose own `name` interpolates the cycle
still diverges.

A type's `name` must be a string. A combinator given a member with a non-string name
refuses by name where it first reads that name; `typedef`, `typedef'`, `enum` and `struct`
refuse a non-string name when applied.

`union` accepts a value when some member's `verify` answers `null`, so it builds each
refusing member's message on the way. Its known limit is loud, never silent: a failing
member whose message itself throws raises that error from `union`'s `verify`, and so can
refuse a value a later member accepts.

### struct

```nix
t.struct "point" { x = t.int; y = t.int; }
```

`.override` tunes three policies:

```nix
(t.struct "point" { x = t.int; y = t.int; }).override {
  total = true;    # every member key must be present (optionalAttr members exempt)
  unknown = true;  # false => reject keys not declared as members (closed world)
  verify = null;   # extra whole-record invariant: value -> null | err
}
```

An override is a **delta over the policy set the receiver was built with**: a field
named in the delta is replaced, a field left unmentioned is retained. The result
carries `.override` again, bound to the new set, so overrides chain at any depth and
`(s.override a).override b` is `s.override (a // b)`.

```nix
# point = t.struct "point" { x = t.int; y = t.int; }

((point.override { total = false; }).override { unknown = false; }).verify { x = 1; }
# => null        (total = false survives the second override)

((point.override { total = false; }).override { total = true; }).verify { x = 1; }
# => "in struct 'point': missing member 'y'"    (same field: the later delta wins)
```

### Custom types

```nix
t.typedef  "even" (v: builtins.isInt v && v / 2 * 2 == v);   # from a bool predicate
t.typedef' "even" (v: if ... then null else "must be even"); # from an option<str> verifier
```

### Refinement contracts

A base checker plus predicate contracts (`{ check = v: bool; message; }`). The base is
verified first, then predicates in a single pass.

```nix
t.refined t.int t.refinements.positive          # int, and > 0
t.refined t.int [ t.refinements.positive t.refinements.tcpPort ]
# t.refinements = { tcpPort; nonEmpty; positive; }
```

### Closed-world key checks

```nix
(t.strict [ "a" "b" ]).verify { a = 1; c = 3; }
# => "keys ['c'] are unrecognized, expected keys are ['a', 'b']"
```

### Validators

A named predicate contract over a kind's instances, collected into an `Either`:

```nix
t.mkValidator {
  name = "positive";
  pred = i: i.n > 0;
  message = "n must be positive";
};
t.runValidators "widget" [ v ] instances;   # { right = instances; } | { left = [failure]; }
t.formatErrors failures;
t.defaultOnError left;                       # throws a formatted error
```

### Conservative equality over checker identity

Two checkers denote the same type when `typeEq` (equivalently `conservativeEq`) holds of
them. The relation is Palmer's **conservative equality** (§2.3, §5.3 — his own term;
"intensional" qualifies the *function*, never the equality), and it dispatches on the
checker's identity REGIME rather than reading a single field:

| regime     | the checker carries           | the relation                                    |
| ---------- | ----------------------------- | ----------------------------------------------- |
| minted     | `__mint.minted`               | digest equality                                 |
| unmintable | `__mint`, no `minted`         | Nix `==` on the checker record **minus `__id`** |
| unmigrated | no `__mint`, no `nestedTypes` | `name` equality                                 |

Every checker this library constructs is stamped. A nixpkgs `lib.types.*` record carries
no `__mint` but does carry `nestedTypes`, and it takes the foreign rule below. So the
**unmigrated** arm now serves only a record that carries neither. `__mint` is a tagged sum,
and a reader that branched on field presence and then read `.minted` raw would abort
uncatchably on a checker that has no mintable identity.

**A foreign (nixpkgs) type is compared, never minted.** A `lib.types.*` record's `name` and
`nestedTypes` claim a constructor without declaring one, so `typeEq` compares the record, the
way the unmintable arm does. A mint over that claim answered `true` for types that accept
different values:

- an `addCheck`'d `int` installed at `types.int` through `lib.extend`, against the stock `int`;
- a record whose `functor.type` is itself (gen-merge's `mkOptionType`), against another with
  the same name and a different check;
- stock `nonEmptyListOf str`, whose `.name` is `listOf`, against `listOf str`.

No narrower mint exists. A foreign record's closures close over its lib instance, and nothing
observable names that instance: source positions name the code, not the environment, and a
lib's `version` does not move under `lib.extend`. The price is that separately built foreign
twins, and one leaf across two lib instances, compare unequal. A type that needs structural
identity is written with this library's constructors, which mint natively. gen-merge's
composites carry no `__mint` yet, so they are compared like any foreign record.

One limit applies: **a hand-grafted comparison across two nixpkgs lib instances can abort.**
When two records share every closure field and differ only in grafted cross-instance data
(`x // { foo = t.port; }` against `x // { foo = u.port; }`), Nix `==` can recurse through a
`functor.type` back-edge until the evaluator overflows its stack, and that abort cannot be
caught. Whether it happens depends on the order in which the evaluator first parsed attribute
names. Records built separately differ in their closures and compare `false` before reaching
the back-edge. Comparisons within one lib instance are unaffected.

### What a checker's identity is minted over

**The construction, never the name.** A checker's preimage is the constructor that built
it plus that constructor's inert argument value. A name is a *rendering* of a type, and a
rendering is lossy — which is not a theoretical worry but a measured collision in four
constructor families at once, all four reading `true` before this landing:

| construction                                               | why the name lost it                                              |
| ---------------------------------------------------------- | ----------------------------------------------------------------- |
| `refined int positive` vs `refined int tcpPort`            | both are named `refined<int>`; the predicates are not in the name |
| `strict [ "a" ]` vs `strict [ "b" ]`                       | *every* strict type is named `"strict"`                           |
| `enum "colour" [ "red" ]` vs `enum "colour" [ "blue" ]`    | the name is the caller's, the members are not in it               |
| `struct "cfg" { a = int; }` vs `struct "cfg" { a = str; }` | likewise for members and the policy set                           |

And it travelled: every combinator builds its name from its members' *names*, so one
colliding member collided the whole tree above it — `listOf<cfg>` merged two different
`cfg`s. A member therefore enters its composite's preimage as its **identity**, and a
composite is structural exactly as deep as its members are.

**Identity is per component.** A type mints over its constructor and its argument
value, in which each member enters as a **tag**: a minted member by its identity, and a **sealed**
one — a member with no minted identity, or one whose `check` a wrapper rewrote (the check-witness
protocol) — as gen-algebra's `sealedMarker`. A constructor's own caller-supplied arguments are sealed
components too: a `typedef`'s predicate, a refinement's `check`, a struct's `verify`. So every
constructor **mints**, and beside the mark the type carries `__sealed`, the map from each sealed
component's path to what a comparison reads: a lambda in its own slot, a registered construction
(gen-algebra `mkIntensional`) as its declared subject, a sealed member as its record (closures first),
and a minted member's own `__sealed` under the member's path (**propagation**). The mark is blind to
`__sealed`, so it is never a key alone:

| construction                                                                 | `__mint`   | `__sealed`                      |
| ---------------------------------------------------------------------------- | ---------- | ------------------------------- |
| primitives, composites over minted members, `enum`, `strict`, `struct`       | **minted** | `{ }`: the mark is the identity |
| `struct(…).override { verify = …; }`                                         | **minted** | `verify`                        |
| `refined base refs`                                                          | **minted** | each `refinements.<i>`          |
| `typedef` / `typedef'`                                                       | **minted** | `pred` / `verify`               |
| a composite over a member with no minted identity, or a rewritten `check`    | **minted** | `members.<i>`                   |
| a self-referential or over-deep type; arguments the encoder refuses (a path) | unmintable | —                               |

**`typeEq` decides over both.** Distinct marks decide `false`; equal marks with `==` sealed maps
decide `true`; equal marks with unequal sealed maps decide `false` where every differing leaf is an
inert registered subject (two different registered constructions) and **refuse by name** otherwise
(gen-algebra `sealedCollisionEq`). So one `typedef` binding declared twice, or two `refined` types over
one stock refinement, is one type; two constructions of one registered term are one type and a
different argument or revision is another; and two separately written lambdas are refused, because
Nix exposes no eliminator for a closure and `==` cannot tell them from one. `__id` refuses a demand
while `__sealed` is non-empty, and `payloadOf` refuses such a record's payload. The identity half is
exported as `mkIdentity ctor members mkArgs sealed name`, so a type built outside this library
(gen-schema's `refined`) is identified by the same construction.

**A caller's predicate is a function or a registered construction**, refused by name at `typedef` and
`typedef'` otherwise, catchably and when the type is built.

The unmintable arm compares the record and never a component list: `check` is a bare
lambda and an attribute selection is an indirection, so a component-wise form is false
even against itself and the relation would be *empty* rather than finer. Finer is the
safe direction here — the failure a type discipline exists to exclude is admitting
semantically distinct values under one type, i.e. answering **true** wrongly.

It compares the record **minus `__id`** and minus nothing else it could detonate on; the type-nesting
guard `__okAt` (below) is excluded too, on a different ground: it is total, but it is an accessor
rather than distinguishing content, and comparing it would force its cells. `__id` is an accessor,
not distinguishing content, and in this regime that accessor *is* the named refusal — so
comparing the record whole would force the refusal inside the very decision it exists to
permit, and the decision would detonate. Excluding the field rather than making it absent
is what keeps the refusal reachable for a consumer that genuinely demands an identity.

**That one exclusion is sufficient, not arbitrary.** `__mint.minted` is the only other
refusal-valued accessor, and it is shielded by the tagged sum's own shape: the minted and
sealed arms live under *different key names*, and Nix `==` decides on the name set before
forcing any value. The one path that does force a mint is a minted-against-minted
comparison, which never reaches this arm — it compares digests, a genuine demand for an
identity, where a catchable named refusal is the right outcome.

`__id` is the accessor for a consumer that DEMANDS an identity: it yields the minted
`"type:<sha256>"` — kind-tagged like every other identity the one mint issues — or it *is*
the named refusal. A consumer that merely decides dispatches instead of demanding.

```nix
t.typeEq (t.listOf t.int) (t.listOf t.int)          # => true
t.typeEq t.int t.str                                # => false
t.typeEq (t.strict [ "a" ]) (t.strict [ "b" ])      # => false  (both named "strict")
t.typeEq (t.refined t.int r.positive)
         (t.refined t.int r.tcpPort)                # => false  (the messages differ in the mark)
t.typeEq (t.refined t.int r.positive)
         (t.refined t.int r.positive)               # => true   (one stock `check`, one slot)
(t.refined t.int r.positive).__id                   # => throws: sealed component(s) 'refinements.0'
```

**A self-referential or over-deep type has no identity, and says so catchably.** A member
enters its composite's preimage as a fixed-width identity, which takes type nesting off the
encoder's depth bound, so type nesting gets its own: 128 levels. A self-referential type is
given no identity at all, and 128 is a chosen refusal point, not a limit inherited from the
evaluator. Each composite carries
`__okAt`, a step-indexed guard whose cell at index k holds when every member's cell at k − 1
does. Reads strictly descend, so a cycle bottoms out at index 0 instead of re-entering its own
mint, and the cells are memoised per node, so the cost is linear in the type graph and never in
its expansion. A cycle and a type nested deeper than 128 levels take the same regime as a
sealed checker: tagged `unmintable`, decided by `typeEq` over the record, and refused by name
when `__id` is demanded. A type between 129 and about 900 deep therefore compares rather than
mints, and gen-merge refuses an identical redeclaration of one by name rather than merging it.

```nix
let r = t.union [ t.int (t.listOf r) ]; in
r.__mint                                            # => { unmintable = { ctor = "union"; … }; }
t.typeEq r r                                        # => true   (the same binding)
r.__id                                              # => throws: a type nests deeper than the
                                                    #    type-identity depth bound (128 levels); …
```

### Reading a construction back

`payloadOf` reads what a checker was constructed from — the preimage its digest was minted
over, `{ ctor; args; }` — and it answers only where that payload re-mints to the digest the
record carries. A sealed checker, a foreign record, and a `//`-derived record carrying its
base's payload under a digest of its own are refused by name, catchably. The payload is
read-only and **bears no identity**: `__mint` decides whether two types are one, and `__id`
answers a demand for an identity.
A composite's `args` hold its members' identities, never the member checkers. Each read
re-runs one `hashIdentity` over the preimage.

```nix
t.payloadOf (t.enum "e" [ "a" ])    # => { ctor = "enum"; args = { name = "e"; elems = [ "a" ]; }; }
t.payloadOf (t.refined t.int r.positive)                  # => throws: its identity is not minted
t.payloadOf (t.int // { inherit (t.enum "e" [ "a" ]) __payload; })
                                    # => throws: its `__payload' is not the preimage of its own digest
```

### The check-witness protocol

A record can state its domain twice: in `verify`, and in a nixpkgs-protocol `check : v -> bool`.
A wrapper (nixpkgs `addCheck`, or `// { check = …; }`) rewrites the second and copies every other
field, `__mint` included, so a reader of the copied identity would take the wrapped type for its
base. **This library owns the protocol that detects the rewrite** (owner ruling, 2026-09-30, open question A
arm (ii)), and every reader of a type's identity consumes it.

| export           | signature                                  | role                                                                              |
| ---------------- | ------------------------------------------ | --------------------------------------------------------------------------------- |
| `witnessedCheck` | `(v -> bool) -> { check; _checkWitness; }` | the constructor: a producer merges it into its record                             |
| `witnessRecord`  | `(v -> bool) -> check`                     | the one record `witnessedCheck` publishes twice, for a producer that publishes it |
| `rewritesCheck`  | `any -> bool`                              | the one test: `true` exactly where the published `check` is no longer the witness |

`witnessedCheck fn` binds one functor record `{ __functor; _fn = fn; }` and publishes it twice, as
`check` and as `_checkWitness`, so the test compares one binding against itself and allocates
nothing. The record is callable: `lib.isFunction` holds of it and `builtins.isFunction` does not.
**`_checkWitness` and `_fn` are protocol fields of this library**: a reader never compares them and
goes through `rewritesCheck`, and a producer spells `_checkWitness` only to publish `witnessRecord`'s
record (below). `rewritesCheck` is total over
records whose `check` reaches weak head normal form: a non-attrset, a record with no witness, and
`{ }` all answer `false`. A `check` that throws when forced throws here too.

```nix
let w = t.witnessedCheck (x: x > 0); own = t.int // w; in
t.rewritesCheck own                                  # => false
t.rewritesCheck (own // { check = _: true; })        # => true
t.rewritesCheck (own // { inherit (own) check; })    # => false  (re-selection is not a rewrite)
t.rewritesCheck t.int                                # => false  (no witness)
```

Where the test holds, this library's readers treat the record as carrying a check its identity does
not state. A combinator (`listOf`, `union`, `struct`, …) carries that `check` beside the member's
`verify`, `idOf` refuses the member by name, so a composite over it takes the unmintable regime,
`identityOf` answers `unmintable`, and `payloadOf` refuses it.

**A producer that publishes the pair itself.** Every call to `witnessedCheck` returns a fresh
two-field set the caller must then read or merge, which costs a producer that builds one type per
declaration a slope per declaration. Such a producer takes the one record from `witnessRecord` and
publishes it under both fields, `check = r; _checkWitness = r;`; `witnessedCheck`'s output stays the
layout it is held to (owner ruling, 2026-09-30). The two spellings are kept in step
by the producer's door, not by construction.

**What the ruling left where it is.** gen-merge's `exportType` is the one producer today, and it
publishes `witnessRecord`'s record itself, held to `witnessedCheck`'s output by its door. Four
per-fold sites in gen-merge restate the test inline for cost rather than call it, each commented as
the protocol's test, and a construction-time agreement door refuses by name when those copies and
this export disagree. Both are part of the arm as ruled, and both are gen-merge's to carry.

**Residue (R1).** A bare checker of this library carries no witness, so `// { check = …; }` over
one is not detected: its `check` is this library's derived assertion `v: v2: …`, not a domain
predicate, and nixpkgs `addCheck` cannot build one (it aborts at `merge`). Only a hand `//` over a
derived field reaches it.

## Handoff to `gen-merge`

The checker record *is* the contract. A merge engine consumes a checker as a leaf's
option type: after merging definitions it calls `t.verify mergedValue` (`null` = ok,
else a blame string) and `t.typeEq` to decide whether two option declarations carry the
same type. **`typeEq`, not `__id`** — deciding is not demanding, and a sealed checker has
an identity to refuse but a record to compare. Where two declarations differ, gen-merge reads
both constructions through `payloadOf` to decide whether a reconciliation law applies
(today: two same-named `enum`s merge to their union). gen-types stays free of any merge/priority
notion — that lives entirely in the engine above it.

## Tests

```console
$ nix develop ./ci --command ci                # guarded
$ nix develop ./ci --command ci --tests-error  # guarded
$ cd ci && nix flake check          # or: nix-unit --flake .#tests — both unguarded
$ cd ci && nix-unit --flake .#testsError        # unguarded
```

`ci` refuses when anything under a declared read root is unknown to git — any extension or name,
`_`-prefixed included — and the remedy is `git add` or a move. The bare `nix-unit --flake ./ci#tests`
and `nix flake check ./ci` are unguarded: they read a git-filtered copy of the tree, so an untracked
cell is silently absent and the run stays green.

207 nix-unit cells on `tests` and 9 on `testsError` across primitives, polymorphic combinators,
structs, refined, validators, strict, identity, the `check` contract, the check-witness protocol,
refusal rendering, and the purity invariant — every
checker with success (`null`) and failure (exact error string) cases, plus nested and
recursive types. The purity test walks `lib/` and fails CI on any `nixpkgs.lib`/
module-system token; it proves it has teeth against an injected violation.

Cells that assert an error's MESSAGE live in `ci/tests-error*.nix`, on the `testsError`
output: `nix flake check` forces every `tests` cell unconditionally, so a cell that throws
on purpose would crash it rather than pass.

## License

MIT © Jason Bowman
