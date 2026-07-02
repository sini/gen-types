# gen-types

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
  __id;    # name-derived intensional identity (sha256, lazy)
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

`.override` tunes three policies (each override starts from defaults):

```nix
(t.struct "point" { x = t.int; y = t.int; }).override {
  total = true;    # every member key must be present (optionalAttr members exempt)
  unknown = true;  # false => reject keys not declared as members (closed world)
  verify = null;   # extra whole-record invariant: value -> null | err
}
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

### Intensional identity

Two checkers denote the same type iff their names agree (Palmer-style, name-only —
no closure/structural comparison). `__id` is the sha256 content address of the name,
the same discipline as gen-schema's `id_hash`.

```nix
t.typeEq (t.listOf t.int) (t.listOf t.int)   # => true
t.typeEq t.int t.str                         # => false
```

## Handoff to `gen-merge`

The checker record *is* the contract. A merge engine consumes a checker as a leaf's
option type: after merging definitions it calls `t.verify mergedValue` (`null` = ok,
else a blame string) and `t.__id` to decide whether two option declarations carry the
same type. gen-types stays free of any merge/priority notion — that lives entirely in
the engine above it.

## Tests

```console
$ cd ci && nix flake check          # or: nix-unit --flake .#tests
```

105 nix-unit assertions across primitives, polymorphic combinators, structs, refined,
validators, strict, identity, the `check` contract, and the purity invariant — every
checker with success (`null`) and failure (exact error string) cases, plus nested and
recursive types. The purity test walks `lib/` and fails CI on any `nixpkgs.lib`/
module-system token; it proves it has teeth against an injected violation.

## License

MIT © Jason Bowman
