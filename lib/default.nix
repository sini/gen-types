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
# a blame string). `t.typeEq` decides whether two checkers carry the same type — `typeEq` and
# not `__id`: deciding is not demanding, and a checker whose content is sealed has an identity
# to REFUSE but a record to compare.
# gen-types is a self-contained LEAF: it must import WITHOUT any registry above
# it, which is why it lives in its own flake rather than inside gen-schema.
#
# Function of a NAMED dep (gen convention §8): the only dependency is gen-prelude's
# pure utility surface. No nixpkgs.lib anywhere under lib/ (purity invariant).
{ prelude, identity }:
let
  inherit (prelude)
    filter
    genAttrs
    ;
  core = import ./checkers.nix { inherit prelude identity; };
  inherit (core)
    checkers
    mkChecker
    mkComposite
    identityGuard
    verifiersOf
    renderNode
    ;
  refinedLib = import ./refined.nix { inherit prelude; };
  validateLib = import ./validate.nix { inherit prelude; };
  strictLib = import ./strict.nix { inherit prelude; };

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
      # ★ A FOREIGN RECORD IS COMPARED, NEVER MINTED (`den-hoag-hc755`; ADR-0034's compared limb).
      # A nixpkgs-protocol record (`nestedTypes` present, no `__mint`) CLAIMS a constructor through
      # its `name` and `nestedTypes` and DECLARES none, and ADR-0034 decides a regime "by
      # CONSTRUCTOR at the declaration". Minting it from that claim is a name-only mint at every
      # node, and it answered `true` for types accepting different values, measured on three
      # routes: an `addCheck`'d `int` installed at `types.int` by `lib.extend` (reflexive, because
      # nixpkgs' `functor.type = lib.types.${name}` is a late-bound lookup); a record whose
      # `functor.type` is itself (gen-merge's `exportType`); and a composite carrying another's
      # name — stock `nonEmptyListOf str` is named `listOf`, and `addCheck (listOf str) f` shares
      # every inert datum with a separately built `listOf str`.
      #
      # ★ WHY NO NARROWER MINT EXISTS. MINTED needs a preimage TOTAL over the distinguishing content
      # (ADR-0034 Consequence 1), and a foreign record's distinguishing content includes its
      # closures' ENVIRONMENT — the lib instance they close over — which has no observable
      # coordinate. Source positions (`unsafeGetAttrPos`) separate CODE, not environment: `listOf
      # str` built from `lib.extend (_: _: { isList = _: false; })` has the stock record's check
      # position, child and name and a different `check [ ]`, and an `mkOptionType { name = "str"; }`
      # installed at `types.str` is reflexive at the stock positions while accepting other values
      # (the same ground `den-hoag-t6iy2`/`xxybl` rejected a position discriminator on). A lib's
      # `version` does not move under `lib.extend`. Structural identity returns only with a
      # lib-instance revision, or with the type written in gen's own vocabulary: this library's
      # constructors mint natively, while gen-merge's composites (`listOf`, `attrsOf`, `nullOr`,
      # `submodule`) carry no `__mint` yet and are compared here like any foreign record.
      #
      # The consequence is deliberate: separately built foreign twins, and one leaf across two lib
      # instances, compare unequal. A record that lacks `__mint` AND `nestedTypes` (the
      # pre-migration population) falls through to the name-only branch below.
      { unmintable = v.name or "<unnamed>"; }
    else
      { unmigrated = v.name; };

  # The comparison SUBJECT for the sealed arm: the reified record MINUS its two accessors,
  # `__id` and `__okAt`, and minus nothing else — preceded by its own closure fields (below).
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
  # ★ CLOSURES FIRST (`den-hoag-6xj95`; ADR-0034's compared limb). The subject is a two-element
  # list: `K`, the record's declared closure fields that are present as functions, then the whole
  # record. List `==` decides index 0 before it touches index 1, and `==` on two functions answers
  # without entering either closure, so a pair whose `K` differs is `false` before any of the
  # record's own attributes is compared. The order matters for records carrying a BACK-EDGE: a
  # nixpkgs record's `functor.type` is a late-bound lookup into its own lib, so across two lib
  # instances (`lib.extend`, or two nixpkgs inputs) attrset `==`, which walks attributes in
  # symbol-interning order, can reach that edge before the first difference and recurse until the
  # evaluator aborts with an UNCATCHABLE stack overflow — on host Nix, Determinate Nix and Lix
  # alike, depending on what text was parsed first. Every nixpkgs `mkOptionType` call builds its
  # own `typeMerge` closure, and so does gen-merge's, so distinct constructions differ in `K`. `K`
  # is a sub-attrset of the record holding the same slots: this is still one `==` over a subject
  # containing the whole reified value, never a component-wise replacement of it.
  #
  # THE VALUE, SCOPED. Where the bare record `==` returns a boolean and every listed field present
  # is total at WHNF, this subject returns the same boolean. Outside that domain the value moves,
  # both ways: a listed field that throws when forced turns a bare `false` into that throw (the
  # `isFunction` filter forces it), and a self-referential nixpkgs type compared across two
  # instances (`let x = either str (listOf x)`) turns `infinite recursion` into `false`.
  #
  # ★ ENUMERATED EXCEPTION TO TOTALITY (ADR-0025 item 1: "enumerated and argued, never silent").
  # The comparison can still abort, uncatchably and depending on interning order, where `K` is
  # EQUAL and the record's `==` then reaches a back-edge before a difference:
  #   1. A GRAFT: every closure slot shared, another attribute holding distinct cross-instance
  #      data — `t.port // { foo = t.port; }` against `t.port // { foo = u.port; }`, or a
  #      `functor` grafted from each instance. Sharing every closure slot means sharing the
  #      construction, and a plain `//`-derivation shares its back-edges too and terminates, so
  #      only a hand graft of cross-instance data reaches this. Foreign COMPOSITES reach it too
  #      since `identityOf` stopped minting them: `let x = listOf str; in x // { foo = t.port; }`
  #      against `x // { foo = u.port; }` aborts depending on interning order, where the mint
  #      used to answer.
  #   2. A record carrying NONE of the listed fields as a function: `K` is `{}` on both sides, the
  #      prefix is vacuously equal and the bare `==` decides alone. A producer whose closure fields
  #      carry other names lands here until this list names them.
  # Closing either needs an evaluator-observable value identity — a visited set — which pure Nix
  # does not expose. Same-instance comparisons take the slot shortcut and are unaffected.
  comparisonSubject =
    v:
    let
      s = removeAttrs v [
        "__id"
        "__okAt"
      ];
      # The closure fields declared by every record producer: nixpkgs' and gen-merge's
      # `mkOptionType`, and this library's `mkChecker`/`mkComposite`.
      sealedKeys = filter (n: s ? ${n} && builtins.isFunction s.${n}) [
        "check"
        "merge"
        "typeMerge"
        "getSubOptions"
        "substSubModules"
        "verify"
        "__nameWithin"
      ];
    in
    [
      (builtins.intersectAttrs (genAttrs sealedKeys (_: null)) s)
      s
    ];

  # CONSERVATIVE EQUALITY — Palmer's own term (§2.3, §5.3); "intensional" qualifies the
  # FUNCTION and never the equality, and the misnomer is what read as a licence to
  # compare intension alone. Palmer's Fig. 5 is a CONJUNCTION over identity AND closure,
  # so a name-only relation ships one half of it and coarsens in the direction §2.3
  # forbids.
  #
  # Where nothing is minted this compares THE REIFIED RECORD — minus
  # `comparisonSubject`'s accessor exclusion — and never a list of components in its place:
  # a projection decides only what it projects, and every attribute the record carries is
  # distinguishing content. (A projection is not false against itself: selecting an attribute
  # keeps its Value slot, so `comparisonSubject`'s closure prefix is `true` for a record
  # against itself; it rides AHEAD of the record, never instead of it.)
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
  # dispatches on the identity REGIME rather than reading a single field, so it covers
  # minted, sealed and not-yet-stamped checkers alike — total but for the sealed arm's
  # enumerated exception at `comparisonSubject`; see its definition above for why the sealed
  # arm compares the whole record and why finer is the safe direction.
  #
  # ★ THE EXPORTED NAME MOVES WITH THE RELATION. `conservativeEq` is Palmer's own term (§2.3,
  # §5.3, §8): "intensional" qualifies the FUNCTION and never the equality, and the name it
  # replaces read as a licence to compare intension alone — which is exactly the half of
  # Fig. 5's conjunction the relation used to ship. `typeEq` stays as the domain-facing
  # spelling, the name a type discipline gives the decision whether two declarations carry
  # the same type.
  typeEq = conservativeEq;
  inherit conservativeEq;

  # ── the type-identity guard, for a producer outside this library ──
  # A construct that mints over a member's `__mint` must step the same index or it reopens the
  # blackhole a self-referential type closes (see `identityGuard` in `./checkers.nix`); gen-schema's
  # `refined` is the one such producer. Exported so the bound and its refusal stay single-sourced.
  inherit identityGuard;
}
