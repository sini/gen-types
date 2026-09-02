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

| Library | Role |
|---------|------|
| [gen-prelude](https://github.com/sini/gen-prelude) | Pure nixpkgs-lib-free utility base (builtins re-exports + vendored lib utils) |
| [gen-algebra](https://github.com/sini/gen-algebra) | Pure primitives (record, search monad, either, intensional identity) |
| [gen-types](https://github.com/sini/gen-types) | **This lib** — Clean-room MIT structural type checker (leaf/poly checkers; `verify: v → null\|err`) |
| [gen-merge](https://github.com/sini/gen-merge) | Byte-mode module merge engine (`evalModuleTree`, byte-identical to nixpkgs `lib.evalModules` over the priority subset) |
| [gen-schema](https://github.com/sini/gen-schema) | Typed registries (kinds, instances, collections, refs); re-hosted on gen-merge |
| [gen-aspects](https://github.com/sini/gen-aspects) | Aspect type system (traits, classification, dispatch); re-hosted on gen-merge |
| [gen-scope](https://github.com/sini/gen-scope) | HOAG scope-graph evaluator (demand-driven, \_eval memoization, circular attributes) |
| [gen-graph](https://github.com/sini/gen-graph) | Accessor-based graph query combinators (traversal, condensation, phaseOrder) |
| [gen-select](https://github.com/sini/gen-select) | Selector algebra (pattern matching over graph positions) |
| [gen-bind](https://github.com/sini/gen-bind) | Module binding (inject external args into NixOS modules) |
| [gen-dispatch](https://github.com/sini/gen-dispatch) | Relational rule dispatch STEP (stratified phases, conflict resolution) |
| [gen-memo](https://github.com/sini/gen-memo) | The incremental plane — decides reuse, never evaluates (change propagation, AFFECTED set) |
| [gen-vars](https://github.com/sini/gen-vars) | Pure-Nix vars/secrets (den-agnostic) |
| [gen-flake](https://github.com/sini/gen-flake) | The nixpkgs boundary — compose purely, inject resolved values, build NixOS systems (value-injection) |

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
  name;    # full structural name, e.g. "listOf<int>"
  verify;  # value -> null | errString      (null = ok)
  check;   # v: v2: throws verify's error on failure, else returns v2
  __name;  # base name with polymorphic metadata stripped ("listOf")
  __mint;  # tagged identity regime: { minted = "type:<sha256>"; } | { unmintable = { ctor; reason; }; }
  __id;    # the accessor for a consumer DEMANDING an identity: the minted value, or a named refusal (lazy)
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

Errors thread context through nesting:

```nix
(t.attrsOf (t.listOf t.int)).verify { a = [ 1 "x" ]; }
# => "in attrsOf<listOf<int>> value: in listOf<int> element:
#     expected type 'int' but value \"x\" is of type 'string'"
```

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
t.mkValidator "positive" (i: i.n > 0) "n must be positive";
t.runValidators "widget" [ v ] instances;   # { right = instances; } | { left = [failure]; }
t.formatErrors failures;
t.defaultOnError left;                       # throws a formatted error
```

### Conservative equality over checker identity

Two checkers denote the same type when `typeEq` (equivalently `conservativeEq`) holds of
them. The relation is Palmer's **conservative equality** (§2.3, §5.3 — his own term;
"intensional" qualifies the *function*, never the equality), and it dispatches on the
checker's identity REGIME rather than reading a single field:

| regime | the checker carries | the relation |
|--------|---------------------|--------------|
| minted | `__mint.minted` | digest equality |
| unmintable | `__mint`, no `minted` | Nix `==` on the checker record **minus `__id`** |
| unmigrated | no `__mint` | `name` equality |

Every checker this library constructs is stamped, so the **unmigrated** arm now serves
only a *foreign* record — one gen-types did not build. `__mint` is a tagged sum, and a
reader that branched on field presence and then read `.minted` raw would abort
uncatchably on a checker that has no mintable identity.

### What a checker's identity is minted over

**The construction, never the name.** A checker's preimage is the constructor that built
it plus that constructor's inert argument value. A name is a *rendering* of a type, and a
rendering is lossy — which is not a theoretical worry but a measured collision in four
constructor families at once, all four reading `true` before this landing:

| construction | why the name lost it |
|---|---|
| `refined int positive` vs `refined int tcpPort` | both are named `refined<int>`; the predicates are not in the name |
| `strict [ "a" ]` vs `strict [ "b" ]` | *every* strict type is named `"strict"` |
| `enum "colour" [ "red" ]` vs `enum "colour" [ "blue" ]` | the name is the caller's, the members are not in it |
| `struct "cfg" { a = int; }` vs `struct "cfg" { a = str; }` | likewise for members and the policy set |

And it travelled: every combinator builds its name from its members' *names*, so one
colliding member collided the whole tree above it — `listOf<cfg>` merged two different
`cfg`s. A member therefore enters its composite's preimage as its **identity**, and a
composite is structural exactly as deep as its members are.

**The regime is decided by the mint, not by a list kept in step by hand.** The encoder is
total: it encodes every node of an inert value or refuses by name. So handing it the
constructor's arguments *is* the classification, and the sealed cases fall out of it —

| construction | regime | because |
|---|---|---|
| primitives, `option`/`listOf`/`attrsOf`/`union`/`intersection`/`tuple`/`optionalAttr`, `enum`, `strict`, `struct` | **minted** | every argument is inert, members entering as their own identities |
| `struct(…).override { verify = …; }` | **unmintable** | the extra invariant is a caller-supplied lambda |
| `refined base refs` | **unmintable** | a refinement's `check` is a caller-supplied lambda |
| `typedef` / `typedef'` | **unmintable** | a caller-declared type is a caller-supplied lambda |

The limbs apply per **component**, which is why the same `struct` constructor mints
without a caller `verify` and seals with one: a single sealed component does not drag its
whole constructor family onto the comparison limb.

**A sealed site owes an argued impossibility, and it is written at each declaration.** Nix
exposes no eliminator for a closure — no builtin reads a captured environment or a body —
so no preimage over one can be total, and an identity over a partial preimage merges
behaviourally distinct checkers. Minting over the name instead is rejected: that is a
name-only identity at a site that mints. **What would have to change is named too**: a
predicate that is a first-order *term* the substrate interprets — a constructor plus an
inert argument — is mint-admissible, and `refined` is the ecosystem's first migration
case. Until it migrates, `typeEq` *decides* about two refined types by comparing their
reified records, which separates them, and demanding `__id` refuses by name.

**That comparison separates two IDENTICAL constructions too, not only different ones**, and
the reach is wider than one checker. `check` is a bare lambda rebuilt on every call, so a
`refined int positive` compares unequal to a second, separately built `refined int positive` — and because a composite over a sealed member is sealed as well, one `refined`
field de-reflexivises the entire struct or list tree above it, at any depth. ADR-0034
declares that precision an allocation artefact, so this is the sealed limb's price rather
than a defect, and it errs in the safe direction: over MINTED members the same composites
still compare equal.

The unmintable arm compares the record and never a component list: `check` is a bare
lambda and an attribute selection is an indirection, so a component-wise form is false
even against itself and the relation would be *empty* rather than finer. Finer is the
safe direction here — the failure a type discipline exists to exclude is admitting
semantically distinct values under one type, i.e. answering **true** wrongly.

It compares the record **minus `__id`**, and minus nothing else. `__id` is an accessor,
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
         (t.refined t.int r.tcpPort)                # => false  (sealed: compares the records)
(t.refined t.int r.positive).__id                   # => throws: a lambda in an identity position
```

## Handoff to `gen-merge`

The checker record *is* the contract. A merge engine consumes a checker as a leaf's
option type: after merging definitions it calls `t.verify mergedValue` (`null` = ok,
else a blame string) and `t.typeEq` to decide whether two option declarations carry the
same type. **`typeEq`, not `__id`** — deciding is not demanding, and a sealed checker has
an identity to refuse but a record to compare. gen-types stays free of any merge/priority
notion — that lives entirely in the engine above it.

## Tests

```console
$ cd ci && nix flake check          # or: nix-unit --flake .#tests
```

136 nix-unit assertions across primitives, polymorphic combinators, structs, refined,
validators, strict, identity, the `check` contract, and the purity invariant — every
checker with success (`null`) and failure (exact error string) cases, plus nested and
recursive types. The purity test walks `lib/` and fails CI on any `nixpkgs.lib`/
module-system token; it proves it has teeth against an injected violation.

## License

MIT © Jason Bowman
