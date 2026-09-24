# gen-types — pure structural type CHECKER for the gen ecosystem.
#
# This is the CHECKING half of a pure-Nix module system: it answers "does this value
# inhabit this type?" and nothing else. A downstream byte-mode MERGE engine (gen-merge)
# sits ABOVE gen-types and consumes these checkers to verify LEAVES — it owns all
# definition merging, priority, and fixpoint. gen-types carries NO merge/priority
# notion whatsoever; the type value is a pure predicate boundary.
#
# The handoff contract is the checker record itself — { name; verify; check; __name;
# __nameWithin; __mint; __id } — so gen-merge calls `t.verify` on a merged leaf value (null = ok, else
# a blame string) and `t.typeEq` to decide whether two option declarations carry the same
# type. `typeEq` and not `__id`: deciding is not demanding, and a checker whose content is
# sealed has an identity to REFUSE but a record to compare.
# gen-types is a self-contained LEAF: it must import WITHOUT any registry above
# it, which is why it lives in its own flake rather than inside gen-schema.
#
# Function of a NAMED dep (gen convention §8): the only dependency is gen-prelude's
# pure utility surface. No nixpkgs.lib anywhere under lib/ (purity invariant).
{ prelude, identity }:
let
  inherit (prelude)
    all
    attrValues
    elem
    any
    map
    ;
  inherit (builtins) isAttrs;
  core = import ./checkers.nix { inherit prelude identity; };
  inherit (core)
    checkers
    mkChecker
    mkComposite
    identityGuard
    typeIdentityDepth
    verifiersOf
    renderNode
    ;
  refinedLib = import ./refined.nix { inherit prelude; };
  validateLib = import ./validate.nix { inherit prelude; };
  strictLib = import ./strict.nix { inherit prelude; };

  # ── foreign (nixpkgs) type structural identity ──
  #
  # An imported `lib.types.*` value carries no `__mint` at all — it is a nixpkgs `mkOptionType`
  # record, not one of this library's own checkers — so `identityOf` below cannot dispatch on
  # `__mint`'s tag for it. Where it carries nixpkgs' own recursive structural field `nestedTypes`
  # (`{}` at a leaf, `{elemType=...}` for `listOf`/`attrsOf`/`nullOr`, `{left;right;}` for `either`,
  # and so on for the rest of the combinator family — `nestedTypes ? {}` is `mkOptionType`'s own
  # default, so every genuine import carries it), route it through this recursive mint instead of a
  # name-only fallback (ADR-0034: "a name-only comparison is rejected anywhere it mints or keys").
  #
  # Mirrors `idOf`/`mkChecker` above: a child enters the parent's preimage as ITS OWN IDENTITY,
  # never as the raw child record — a composite is structural exactly as deep as its members are,
  # and the walk never applies or walks `.check`/`.merge` at any depth. It reads `.name` and
  # `.nestedTypes`, and at a registry leaf it compares `.functor.type` (nixpkgs' one
  # self-referential field) against the leaf itself under `==`, never descending into it (below).
  #
  # ★ LEAF CLASSIFICATION IS BY REGISTRY, NOT BY "EMPTY `nestedTypes`" ALONE (gate finding,
  # `den-hoag-2e3cc`). Driven over twelve nixpkgs combinator families: five reach empty
  # `nestedTypes` while their distinguishing content lives in a `check`/`merge` closure this walk
  # never inspects — `enum`, `addCheck`'s result, `ints.between`, `submodule`, `separatedString` —
  # and an unconditional "empty ⇒ leaf, mint by name" rule mints two genuinely distinct instances of
  # each identically. The registry below is the finite set of nixpkgs' own leaf names measured
  # genuinely first-order at the pinned rev; `path` is gate-suggested and EXCLUDED on measurement —
  # `pathWith`'s three callers (`path`, `pathInStore`, `externalPath`) all produce the identical
  # hardcoded `.name == "path"` while differing in accept/reject behaviour, so registering it would
  # reproduce this construction's own target defect one layer down (spec §2).
  #
  # A name outside the registry, or a composite with a sealed member anywhere in it, takes
  # ADR-0034's sealed-limb treatment: no identity minted, tagged `unmintable` so `identityOf` routes
  # it to `conservativeEq`'s existing full-record comparison — the same decision that regime already
  # carries, with no new dispatch branch needed.
  #
  # ★ A REGISTRY NAME IS NECESSARY, NOT SUFFICIENT: THE LEAF MUST ALSO BE ITS OWN LIB'S BINDING AT
  # THAT NAME (`den-hoag-0x4hh`). nixpkgs' `addCheck` returns `elemType // { check; merge; }`, and a
  # raw `str // { check = …; }` does the same, so both keep the base's `name`, empty `nestedTypes`
  # and `functor` while accepting different values. Registry membership alone minted every such
  # record as the bare leaf, and `typeEq` answered `true` for two types that accept different
  # values. The added predicate is a lambda and cannot enter the preimage (ADR-0034), so the leaf
  # test adds one inert datum: constructor reflexivity, `t.functor.type == t`. A record that fails
  # it takes the sealed path above and is decided by COMPARISON (ADR-0034's compared regime), which
  # is finer than equality: two separately built `addCheck str f` with the same `f` also compare
  # unequal. The conjunct only withholds mints, so its one possible error is toward COMPARED.
  foreignLeafRegistry = [
    "str"
    "int"
    "bool"
    "float"
    "anything"
    "raw"
    "unspecified"
    "attrs"
    "package"
  ];

  foreignWithin =
    d: t:
    d <= typeIdentityDepth
    && all (foreignWithin (d + 1)) (if isAttrs t then attrValues (t.nestedTypes or { }) else [ ]);

  # ★ WHAT THE LEAF TEST'S REFLEXIVITY CONJUNCT CERTIFIES, AND ITS ARGUED LIMIT. nixpkgs'
  # `defaultFunctor` sets `type = lib.types.${name} or null`: a LATE-BOUND NAME LOOKUP in the
  # record's own lib fixpoint, not an inert constructor datum. So `t.functor.type == t` certifies
  # "t is its own lib's binding at `t.name`", not "t is the constructor's output". A check-carrying
  # record INSTALLED AT ITS OWN NAME, e.g.
  # `lib.extend (_: p: { types = p.types // { int = p.types.addCheck p.types.int f; }; })`,
  # is reflexive, still mints as `int`, and still collapses against the genuine leaf and against a
  # differently-checked install. That residue predates the conjunct and is filed as
  # `den-hoag-hc755`. The claim this construction makes is scoped to records NOT bound at
  # `lib.types.<name>`; silence here would not be a classification (ADR-0034).
  mintForeign =
    t:
    let
      children = attrValues (t.nestedTypes or { });
      mintedChildren = map mintForeign children;
    in
    if children == [ ] then
      if elem t.name foreignLeafRegistry && ((t.functor or { }).type or null) == t then
        {
          minted = identity.hashIdentity "type" [ "name" "children" ] (
            l:
            {
              name = t.name;
              children = [ ];
            }
            .${l}
          );
        }
      else
        { sealed = t.name; }
    else if any (m: m ? sealed) mintedChildren then
      { sealed = t.name; }
    else
      {
        minted = identity.hashIdentity "type" [ "name" "children" ] (
          l:
          {
            name = t.name;
            children = map (m: m.minted) mintedChildren;
          }
          .${l}
        );
      };

  # The ONE access discipline over the three identity regimes, and it is TOTAL OVER
  # THOSE THREE REGIMES — not over the two populations of the migration window, which
  # is the narrower claim it replaced and which omits the sealed regime entirely.
  # `__mint` is a TAGGED SUM, so no reader may branch on FIELD PRESENCE and then read
  # `.minted` raw: on a value that has no mintable identity `v ? __mint` holds and
  # `.minted` is absent, and that read aborts uncatchably rather than refusing. That is
  # also why the readers below stop reading `__id`: `__id` is the accessor for a
  # consumer that DEMANDS an identity, and demanding one of a sealed checker is a
  # refusal — so a reader that DECIDES must dispatch on the tag instead of demanding.
  #
  #   minted     — an identity over a preimage total in the checker's distinguishing
  #                content; the digests decide.
  #   unmintable — no identity and no substitute; the decision compares the reified
  #                checker record.
  #   unmigrated — the migration window: no producer has stamped this checker, so its
  #                name is still all the decision has. This arm stays live until the
  #                producer lands, and while it is live the relation is byte-for-byte
  #                the shipped one — `__id` was a pure function of `name`.
  identityOf =
    v:
    if v ? __mint && v.__mint ? minted then
      { inherit (v.__mint) minted; }
    else if v ? __mint then
      { inherit (v.__mint) unmintable; }
    else if v ? nestedTypes then
      # A genuine nixpkgs import (§ "foreign (nixpkgs) type structural identity" above): structural
      # identity through the recursive mint, never name alone. A record that merely lacks `__mint`
      # AND `nestedTypes` (the pre-migration population this arm still covers) falls through to the
      # unchanged name-only branch below.
      #
      # ★ A nixpkgs record cannot carry the step-indexed memo, and `mintForeign` is unmemoised
      # already, so the foreign branch takes a depth-bounded walk over `nestedTypes` first: a cyclic
      # or over-deep foreign type is sealed rather than overflowing the stack inside the mint.
      let
        m = if foreignWithin 0 v then mintForeign v else { sealed = v.name or "<unnamed>"; };
      in
      if m ? minted then { inherit (m) minted; } else { unmintable = m.sealed; }
    else
      { unmigrated = v.name; };

  # The comparison SUBJECT for the sealed arm: the reified record MINUS its two accessors,
  # `__id` and `__okAt`, and minus nothing else.
  #
  # ★ `__id` IS AN ACCESSOR, NOT DISTINGUISHING CONTENT, and in the sealed regime that
  # accessor IS the named refusal. Comparing the record without excluding it forces the
  # refusal inside a decision the refusal exists to permit, and the decision detonates.
  # Measured on a sealed checker carrying a throwing `__id`: self-comparison of the
  # unexcluded record ABORTS, and a distinct pair survives only because a lambda-valued
  # attribute happens to be compared first and short-circuits — an ordering accident,
  # not a property. Excluding the accessor removes both.
  #
  # ★ The alternative — making `__id` ABSENT on a sealed checker — is rejected: it would
  # delete the named refusal a consumer that DEMANDS an identity must receive, trading a
  # detonation for a silent missing attribute.
  #
  # `removeAttrs` preserves the evaluator's cell fast path (measured: a record compared
  # with itself through it stays equal, two separately-built records stay unequal, and
  # on a record with no `__id` it is a byte-for-byte no-op), so this excludes the
  # accessor without emptying the relation.
  #
  # ★ WHY EXCLUDING `__id` IS SUFFICIENT AND NOT ARBITRARY. It is the only OTHER
  # refusal-valued accessor a compared value can carry, because `__mint.minted` is
  # shielded by the tagged sum's own shape: the minted and sealed arms live under
  # DIFFERENT KEY NAMES, and Nix `==` decides on the name set before forcing any value.
  # Measured, with its control: a throwing payload under a differently-named key is
  # never reached, while the SAME name on both sides DOES force — so the short-circuit
  # is the name check, not throws being ignored. Two sealed values carry inert payloads
  # under one name, so nothing forces there either. The one path that does force a mint
  # is a minted-against-minted comparison, and that arm never reaches here: it compares
  # digests, which is a genuine DEMAND for an identity, where a catchable named refusal
  # is the correct outcome rather than a hazard.
  #
  # ★ `__okAt` IS EXCLUDED BESIDE IT, on a different ground: it is total (a cyclic type's stream
  # bottoms out at index 0), so nothing detonates, but it is an accessor rather than distinguishing
  # content, and comparing it would force up to `typeIdentityDepth + 1` cells of each side.
  #
  # ★ ENUMERATED EXCEPTION TO TOTALITY (ADR-0025 item 1: "enumerated and argued, never silent";
  # `den-hoag-6xj95`). The `==` this subject feeds is NOT total over FOREIGN records drawn from TWO
  # DISTINCT nixpkgs lib instances (`lib.extend`, or two nixpkgs inputs). A nixpkgs record's
  # `functor.type` points back at a leaf record of its own lib, Nix compares attributes in
  # symbol-interning order, and when `functor` is interned before the first differing attribute
  # the comparison recurses until the evaluator aborts with an UNCATCHABLE stack overflow. Whether
  # it aborts or answers `false` therefore depends on what text the evaluator parsed first, on host
  # Nix, Determinate Nix and Lix alike. The class: ANY cross-instance pair that reaches this arm
  # may abort. Measured to abort in at least one order: `port`, `ints.between 0 1`, `nonEmptyStr`,
  # and each registry leaf wrapped by `addCheck` or `//`, which the reflexivity conjunct in
  # `mintForeign` sends here rather than minting as the leaf. Measured to answer `false` in every
  # order: `path`, `enum`. This file's own text shifts the order: with the conjunct's `functor`
  # identifier parsed before nixpkgs' types, cross-instance `port`, `ints.between` and
  # `nonEmptyStr` go from `false` to an overflow even with no prefix.
  # Same-instance comparisons are unaffected: a shared `functor` Value takes the pointer shortcut.
  # Argued: what the conjunct replaced for the `addCheck`/`//` population is a SILENT `true` for
  # types that accept different values, a name-only mint ADR-0034 rejects, and an abort is loud
  # where that answer was silent. The repair, breaking the `functor.type` cycle at every depth,
  # belongs to this binding and is `den-hoag-6xj95`.
  comparisonSubject =
    v:
    removeAttrs v [
      "__id"
      "__okAt"
    ];

  # CONSERVATIVE EQUALITY — Palmer's own term (§2.3, §5.3); "intensional" qualifies the
  # FUNCTION and never the equality, and the misnomer is what read as a licence to
  # compare intension alone. Palmer's Fig. 5 is a CONJUNCTION over identity AND closure,
  # so a name-only relation ships one half of it and coarsens in the direction §2.3
  # forbids.
  #
  # Where nothing is minted this compares THE REIFIED RECORD — minus
  # `comparisonSubject`'s one exclusion — and never a list of components: `check` is a
  # bare lambda and an attribute selection is an indirection, so a component-wise form
  # is false even against itself and the relation would be EMPTY rather than finer.
  # Finer is the safe direction for a type-equality decision — the failure a type
  # discipline exists to exclude is admitting semantically distinct values under one
  # type, i.e. returning TRUE wrongly.
  conservativeEq =
    a: b:
    let
      ia = identityOf a;
      ib = identityOf b;
    in
    if ia ? minted && ib ? minted then
      ia.minted == ib.minted
    else if ia ? unmigrated && ib ? unmigrated then
      ia.unmigrated == ib.unmigrated
    else
      comparisonSubject a == comparisonSubject b;
in
# The checker constructor set IS the public surface; the fold-ins (refined/strict/
# validators) and the identity helpers ride alongside it.
checkers
// {
  # refinement contracts
  refined = refinedLib.refined {
    inherit
      mkComposite
      verifiersOf
      renderNode
      ;
  };
  inherit (refinedLib) refinements;

  # closed-world unknown-key rejection
  strict = strictLib.strict mkChecker;

  # validator base (predicate contracts over a kind's instances)
  inherit (validateLib)
    mkValidator
    runValidators
    formatErrors
    defaultOnError
    ;

  # ── conservative equality over checker identity ──
  # Two checkers denote the same type when `conservativeEq` holds of them. The relation
  # dispatches on the identity REGIME rather than reading a single field, so it is total
  # over minted, sealed and not-yet-stamped checkers alike; see its definition above for
  # why the sealed arm compares the whole record and why finer is the safe direction.
  #
  # ★ THE EXPORTED NAME MOVES WITH THE RELATION. `conservativeEq` is Palmer's own term (§2.3,
  # §5.3, §8): "intensional" qualifies the FUNCTION and never the equality, and the name it
  # replaces read as a licence to compare intension alone — which is exactly the half of
  # Fig. 5's conjunction the relation used to ship. `typeEq` stays as the domain-facing
  # spelling, since gen-merge consumes this to decide whether two option declarations carry
  # the same type and names it the way a type discipline would.
  typeEq = conservativeEq;
  inherit conservativeEq;

  # ── the type-identity guard, for a producer outside this library ──
  # A construct that mints over a member's `__mint` must step the same index or it reopens the
  # blackhole a self-referential type closes (see `identityGuard` in `./checkers.nix`); gen-schema's
  # `refined` is the one such producer. Exported so the bound and its refusal stay single-sourced.
  inherit identityGuard;
}
