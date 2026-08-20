# gen-types — agent capability sheet

## Scope

Pure, `nixpkgs.lib`-free structural type CHECKER: every constructor returns a record whose `verify` maps a value to `null` (inhabits the type) or an error string (does not). No merging, no priorities, no fixpoint.

## Not this library's job

Quoted text is the owner's own `flake.nix` `description` field, verbatim.

| Responsibility | Owner |
|---|---|
| Merging definitions, priority, fixpoint, `evalModules` | `gen-merge` — "gen-merge — pure-Nix byte-mode module MERGE engine (evalModuleTree) for the pure-gen module system". gen-merge takes gen-types as an input and injects it as `types` (`gen-merge/flake.nix:13,25`); its union dispatch prefers a gen-types leaf's `verify` over its own `check` (`gen-merge/lib/types.nix:355-357`) |
| Registries — kinds, instances, collections, refs — and minting ENTITY identity (`id_hash`) | `gen-schema` — "gen-schema: typed record registry with extension points for the pure-gen module system". The seam: gen-types hashes a TYPE NAME only (`hashString "sha256" "gen-types\|${name}"`, `lib/checkers.nix:131`); gen-schema hashes kind + content (`gen-schema/lib/identity.nix:18`). gen-types VALIDATES a value; gen-schema REGISTERS a record and mints its identity |
| Field-aware validator wrappers and the kind-driven `validateInstances` entry point (gen-types ships the validator BASE only) | `gen-schema` — same description; the split is stated at `lib/validate.nix:7-10`, and `validateInstances` is exported at `gen-schema/lib/default.nix:73` |
| General utilities — gen-types' sole dependency (`flake.nix:10`) | `gen-prelude` — "gen-prelude: vendored, nixpkgs-lib-free pure utilities for the gen ecosystem" |
| Search monad, records, either, intensional-function construction; gen-types inlines its own conservative-equality dispatch (`lib/default.nix`, bindings `identityOf`/`conservativeEq`) and takes no gen-algebra input | `gen-algebra` — "gen-algebra: pure Nix algebra — search monad, records, intensional functions, either" |
| Aspect traits / classification | `gen-aspects` — "gen-aspects: aspect-oriented composition types (pure-gen, re-hosted on gen-merge)" |
| Matching values by graph POSITION rather than by shape | `gen-select` — "gen-select: selector algebra for attributed graph positions" |
| Scope-graph evaluation, attribute demand | `gen-scope` — "gen-scope: demand-driven attribute grammar evaluator over algebraic scope graphs" |
| Layered settings resolution, provenance, refs-as-data | `gen-settings` — "gen-settings — stratified settings resolution as a pure layered fold, with refs-as-data, structured provenance, and the graduated injection construct" |
| The nixpkgs boundary, value injection, building systems | `gen-flake` — "gen-flake — the pure composition boundary of the pure-gen module ecosystem" |

## Exports

Entry: `inputs.gen-types.lib` (flake, `flake.nix:16`). Root `default.nix` is a FUNCTION of a named dep — `import ./. { prelude = <gen-prelude.lib>; }` — with a default that fetches the flake-locked gen-prelude, so the plain-import path stays in lockstep with the flake output.

**Checker record** (the value every constructor returns; fields, not lib exports)

| Field | Meaning |
|---|---|
| `name` | full structural name, e.g. `"listOf<int>"` |
| `verify` | `value -> null \| errString` (`null` = ok) |
| `check` | `v -> v2 -> v2`, throwing `verify v`'s error on failure |
| `__name` | base name, polymorphic metadata stripped (`"listOf"`) |
| `__id` | `sha256` of `"gen-types\|${name}"` |
| `override` | present on `struct` results ONLY (`lib/checkers.nix:328`) |
| `__refinements` | present on `refined` results ONLY (`lib/refined.nix:56`) |

**Primitives** — `lib/checkers.nix`. Each is a `checker` value, not a function.

| Export | Accepts |
|---|---|
| `string` / `str` | `isString` (`str` is a definitional alias; both name `"string"`) |
| `int`, `bool`, `float` | `builtins.is{Int,Bool,Float}` |
| `number` | int or float |
| `path` | `isPath` |
| `pathLike` | path, derivation, or string |
| `attrs`, `list`, `function` | `isAttrs` / `isList` / `isFunction` |
| `derivation` | attrset with `type == "derivation"` |
| `null` | `v == null` |
| `any` | everything |
| `never` | nothing |

**Polymorphic combinators** — `lib/checkers.nix`

| Export | Signature |
|---|---|
| `option` | `checker -> checker` (`null`, or the base) |
| `listOf` / `attrsOf` | `checker -> checker` |
| `union` / `intersection` | `[checker] -> checker` |
| `enum` | `name -> [value] -> checker` (membership by `==`) |
| `tuple` | `[checker] -> checker` (positional, length-exact) |
| `optionalAttr` | `checker -> checker` (flags a struct member omittable) |
| `struct` | `name -> { <member> = checker; } -> checker`, starting from the policy set `total = true`, `unknown = true`, `verify = null`; `.override delta` replaces the fields `delta` names, retains the rest, and rebinds `.override` over the new set (chainable) |

**Custom constructors** — `lib/checkers.nix`

| Export | Signature |
|---|---|
| `typedef` | `name -> (v -> bool) -> checker` |
| `typedef'` | `name -> (v -> null \| err) -> checker` |

**Refinement contracts** — `lib/refined.nix`

| Export | Signature |
|---|---|
| `refined` | `checker -> (refinement \| [refinement]) -> checker`; a refinement is `{ check = v -> bool; message; }` |
| `refinements` | `{ nonEmpty; positive; tcpPort; }` — the stock predicate records |

**Closed-world keys** — `lib/strict.nix`

| Export | Signature |
|---|---|
| `strict` | `[str] -> checker` (rejects keys outside the list) |

**Validators** — `lib/validate.nix`

| Export | Signature |
|---|---|
| `mkValidator` | `name -> pred -> message -> { name; pred; message; }` |
| `runValidators` | `kind -> [validator] -> { <name> = instance; } -> { right = instances; } \| { left = [failure]; }` |
| `formatErrors` | `[failure] -> str` |
| `defaultOnError` | `left -> throws` |

**Identity** — `lib/default.nix`

| Export | Signature |
|---|---|
| `typeEq` / `conservativeEq` | `checker -> checker -> bool` (conservative equality, dispatched on the checker's `__mint` tag; the two are the same function). `conservativeEq` is Palmer's own term — *intensional* qualifies the FUNCTION, never the equality |

## Entry points by task

| Task | Reach for |
|---|---|
| Ask whether a value inhabits a type | `t.<type>.verify v` — `null` means ok |
| Validate and pass a value through | `t.<type>.check v v2` |
| A record with named fields | `t.struct "name" { <member> = t.<type>; }` |
| Reject undeclared record keys | `(t.struct …).override { unknown = false; }`, or standalone `t.strict [ "a" "b" ]` |
| Let a record key be absent | `t.optionalAttr t.<type>` as the member, or `.override { total = false; }` |
| A whole-record invariant | `.override { verify = r: …; }` |
| A new type from a bool predicate | `t.typedef "even" pred` |
| A new type with a custom message | `t.typedef' "even" (v: … null \| err)` |
| Constrain a value's range/domain | `t.refined t.int t.refinements.positive` |
| A predicate contract over a kind's instances | `t.mkValidator` + `t.runValidators`, then `t.formatErrors` / `t.defaultOnError` |
| Decide whether two types are the same | `t.typeEq a b` — conservative equality, regime-dispatched; see traps |
| Hand a leaf type to the merge engine | pass the checker record itself; gen-merge calls `.verify` and `.__id` |
| Use outside a flake | `import <gen-types> { prelude = …; }` |

## Measured traps

Every row verified in this run by evaluating against `.#lib` (`t`). Shared fixtures: `s = t.struct "point" { x = t.int; y = t.int; }`; `rp = t.refined t.int t.refinements.positive`; `rt = t.refined t.int t.refinements.tcpPort`; `v = t.mkValidator "positive" (i: i.n > 0) "n must be positive"`.

| Trap | Evidence |
|---|---|
| `verify` returns `null` for SUCCESS, so the success sentinel and the `null` type's inhabitant are the same value | `lib/checkers.nix:166`; `t.null.verify null` ⇒ `null`, `t.null.verify 5` ⇒ `"expected type 'null' but value 5 is of type 'int'"` |
| `check` is 2-arity and checks only its FIRST argument; the second is returned unexamined | `lib/checkers.nix:139-144`; `t.int.check 5 "not-an-int"` ⇒ `"not-an-int"`; `t.int.check "x" 5` threw. Tests: `test-check-returns-second-on-success`, `test-check-throws-on-failure`, `test-check-identity-usage` (`ci/tests/types-check.nix`) |
| `unknown` polarity reads backwards: `unknown = true` (the default) PERMITS undeclared keys | `lib/checkers.nix:269,276,323`; `s.verify { x = 1; y = 2; z = 3; }` ⇒ `null`; with `unknown = false` ⇒ `"in struct 'point': keys ['z'] are unrecognized, expected keys are ['x', 'y']"`. Tests: `test-unknown-allowed-by-default`, `test-unknown-rejected-when-closed` (`ci/tests/types-struct.nix`) |
| No producer stamps `__mint`, so every shipped checker takes the **unmigrated** arm and `typeEq` is `name` equality — any two types sharing a name are `typeEq` regardless of content. Four collisions observed: `refined` names only the base (`refined<int>`), `strict` names the constant `"strict"`, `enum`/`struct` names are caller-supplied. The regime dispatch is in place; the producer that would retire this arm is not landed | `lib/checkers.nix`, binding `mkId`; `lib/default.nix`, binding `conservativeEq`; `lib/refined.nix:45`, `lib/strict.nix:26`; `t.typeEq rp rt` ⇒ `true`; `t.typeEq (t.strict [ "a" ]) (t.strict [ "b" ])` ⇒ `true`; `t.typeEq (t.enum "color" [ "red" ]) (t.enum "color" [ "blue" ])` ⇒ `true`; `t.typeEq (t.struct "p" { x = t.int; }) (t.struct "p" { y = t.str; })` ⇒ `true`. Positive control, same predicate: `t.typeEq (t.listOf t.int) (t.listOf t.str)` ⇒ `false`, `t.typeEq (t.listOf t.int) (t.listOf t.int)` ⇒ `true`. Tests: `test-typeEq-different-names`, `test-typeEq-nested-distinct` (`ci/tests/types-identity.nix`) |
| `enum`'s first argument IS the whole type name — no `enum<…>` wrapper is synthesized | `lib/checkers.nix:225-230`; `(t.enum "color" [ "red" ]).name` ⇒ `"color"`; failure ⇒ `"\"red\" is not a member of enum 'color'"` |
| The `optionalAttr` exemption from `total` is POSITIONAL — only a member whose `__name` is exactly `"optionalAttr"`; any wrapping loses it | `lib/checkers.nix:304`; `(t.struct "s" { a = t.optionalAttr t.int; }).verify { }` ⇒ `null`, but `(t.struct "s2" { a = t.option (t.optionalAttr t.int); }).verify { }` ⇒ `"in struct 's2': missing member 'a'"`. Positive control, plain member: `(t.struct "s3" { a = t.int; }).verify { }` ⇒ `"in struct 's3': missing member 'a'"`. Test: `test-optional-member-absent-ok` (`ci/tests/types-struct.nix`) |
| `listOf` / `attrsOf` blame names neither the index nor the key; `tuple` alone reports a position | `lib/checkers.nix:187,201,248`; `(t.listOf t.int).verify [ 1 "x" 2 ]` ⇒ `"in listOf<int> element: expected type 'int' but value \"x\" is of type 'string'"`; `(t.attrsOf t.int).verify { a = 1; b = "x"; }` ⇒ `"in attrsOf<int> value: …"`; `(t.tuple [ t.int t.str ]).verify [ 1 2 ]` ⇒ `"in tuple<int, string>: in element 1: …"` |
| `union` failure blames no member — it reports only the union's own type error | `lib/checkers.nix:212`; `(t.union [ t.int t.str ]).verify true` ⇒ `"expected type 'union<int,string>' but value true is of type 'bool'"` |
| Empty-list combinators go opposite ways: `union [ ]` rejects everything, `intersection [ ]` accepts everything | `lib/checkers.nix:212,222`; `(t.union [ ]).verify 1` ⇒ `"expected type 'union<>' but value 1 is of type 'int'"`, `(t.intersection [ ]).verify 1` ⇒ `null` |
| `refined` adds NO context frame: a base failure surfaces unwrapped, and a predicate failure is the bare `message` | `lib/refined.nix:47-53`; `rp.verify "x"` ⇒ `"expected type 'int' but value \"x\" is of type 'string'"` (no `refined<int>` prefix), `rp.verify (-1)` ⇒ `"must be positive"`, `rt.verify (-1)` ⇒ `"must be a valid TCP port (1-65535)"`. Test: `test-base-checked-first` (`ci/tests/types-refined.nix`) |
| `pathLike` accepts ANY string | `lib/checkers.nix:161`; `t.pathLike.verify "not a path"` ⇒ `null`. Positive control, same instrument: `t.path.verify "not a path"` ⇒ `"expected type 'path' but value \"not a path\" is of type 'string'"` |
| `derivation` is a duck-type test, not a store check | `lib/checkers.nix:55,165`; `t.derivation.verify { type = "derivation"; }` ⇒ `null` |
| `str` never appears in output — it is a definitional alias, so both the name and the blame say `string` | `lib/checkers.nix:154-155`; `t.str.name` ⇒ `"string"`, `t.str.verify 1` ⇒ `"expected type 'string' but value 1 is of type 'int'"`. Test: `test-str-alias-shares-identity` (`ci/tests/types-identity.nix`) |
| `runValidators` takes instances as an ATTRSET keyed by instance name. Passing a LIST aborts the whole evaluation with an error `builtins.tryEval` does not trap | `lib/validate.nix:27-30`; `builtins.tryEval (builtins.attrNames (t.runValidators "widget" [ v ] [ { n = 1; } ]))` did not return — eval failed with `error: expected a set but found a list`. Contrast, same instrument: `tryEval` DID trap `t.defaultOnError …` and `(t.union t.int).verify 1`. Positive control, attrset form: `attrNames (t.runValidators "widget" [ v ] { a = { n = 1; }; })` ⇒ `["right"]`; failing form ⇒ `left = [ { kind = "widget"; name = "a"; validator = "positive"; message = "n must be positive"; } ]`. Tests: `test-runValidators-right`, `test-runValidators-left` (`ci/tests/types-validate.nix`) |
| `union` / `intersection` / `tuple` / `struct` assert their argument shape at CONSTRUCTION, before any value is seen | `lib/checkers.nix:207,217,235,285`; `(t.union t.int).verify 1` threw |
| Name separators are inconsistent, and `name` is what feeds `__id` | `lib/checkers.nix:209,219,237`; `(t.tuple [ t.int t.str ]).name` ⇒ `"tuple<int, string>"` (comma-space) vs `(t.union [ t.int t.str ]).name` ⇒ `"union<int,string>"` (bare comma) |
| `defaultOnError` never returns — both of its branches throw | `lib/validate.nix:52-57`; `tryEval` on it ⇒ `success = false`. Test: `test-defaultOnError-throws` (`ci/tests/types-validate.nix`) |
| Frugality — single-pass happy path, rescan only to locate a failure, lazy `__id` | `lib/checkers.nix:91-131`, `lib/refined.nix:23-36`: read, NOT exercised in this run (no allocation or forcing instrument was applied) |

## Theory

The README states no result and carries no Implements/Informed-by split; the citations below are the ones the repo's own comments and README make.

**Claims**

- **Findler & Felleisen (2002), contracts** — `lib/checkers.nix:4-7` calls a type "a boundary that blames the value on mismatch", restricted to a first-order core; `README.md:8-10` states the same as "a type is a predicate boundary".
- **Palmer's conservative equality (§2.3, §5.3)** — `lib/default.nix`, bindings `identityOf` and `conservativeEq`, which `typeEq` is an alias of. The relation dispatches on the checker's `__mint` tag over three regimes (minted / unmintable / unmigrated) rather than reading one field. Fig. 5 is a **conjunction** over identity AND closure, so a name-only relation ships one conjunct and coarsens in the direction §2.3 forbids; it survives here only on the unmigrated regime, which is where every shipped checker currently sits — `lib/checkers.nix`, binding `mkId`, still derives `__id` from `name` alone, and no producer stamps `__mint` yet. The unmintable arm compares the checker record **minus `__id`** (binding `comparisonSubject`), never a component list — `__id` is an accessor, and in that regime it *is* the named refusal, so comparing the record whole forces the refusal inside the decision it exists to permit. That one exclusion suffices: `__mint.minted` is the only other refusal-valued accessor and the tagged sum shields it, its minted and sealed arms living under different key names, which Nix `==` decides on before forcing any value.
- **The `id_hash` discipline of gen-schema** — `README.md` § *Conservative equality over checker identity* and `lib/checkers.nix`, binding `mkId`, state `__id` uses the same hashing discipline. Cross-repo citation.

**Influences** (named in comments, no result claimed)

- **Rondon, Kawaguchi & Jhala (2008), liquid types** — `lib/refined.nix:3-4` cites the style of co-locating predicates with the base type, not the inference algorithm.

**Checked invariant**: `lib/` is `nixpkgs.lib`-free and module-system-free. Enforced by `ci/tests/types-purity.nix`, which also arms its own oracle — `test-detector-catches-injected-violation` runs the scanner against a planted violation, alongside `test-library-source-is-dependency-free`.

## Drift check

```sh
nix eval --json .#lib --apply 'l: { top = builtins.attrNames l; refinements = builtins.attrNames l.refinements; }'
```

Current output (verbatim):

```json
{"refinements":["nonEmpty","positive","tcpPort"],"top":["any","attrs","attrsOf","bool","conservativeEq","defaultOnError","derivation","enum","float","formatErrors","function","int","intersection","list","listOf","mkValidator","never","null","number","option","optionalAttr","path","pathLike","refined","refinements","runValidators","str","strict","string","struct","tuple","typeEq","typedef","typedef'","union"]}
```

`refinements` is the only nested namespace of exports on `lib` (nullary checker records are attrsets too; an `isAttrs` sweep returns 16 names). `override` and `__refinements` are fields of returned checker VALUES, not exports, so they do not appear above.

**Checks.** Test-runner invocation (from the repo root; CI runs the same command with `working-directory: ci`, `.github/workflows/ci.yml:11-13,18`):

```sh
nix flake check ./ci
```
