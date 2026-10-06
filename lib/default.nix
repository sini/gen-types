# gen-types — pure structural type CHECKER for the gen ecosystem.
#
# This is the CHECKING half of a pure-Nix module system: it answers "does this value
# inhabit this type?" and nothing else. A downstream byte-mode MERGE engine (gen-merge)
# sits ABOVE gen-types and consumes these checkers to verify LEAVES — it owns all
# definition merging, priority, and fixpoint. gen-types carries NO merge/priority
# notion whatsoever; the type value is a pure predicate boundary.
#
# The handoff contract is the checker record itself — { name; verify; check; __name;
# __nameWithin; __mint; __payload; __sealed } — so gen-merge calls `t.verify` on a merged leaf value (null = ok,
# else a blame string). `t.typeEq` decides whether two checkers carry the same type — `typeEq` and
# not `idOf`: deciding is not demanding, and a checker whose content is sealed has an identity
# to REFUSE but a record to compare.
# gen-types is a self-contained LEAF: it must import WITHOUT any registry above
# it, which is why it lives in its own flake rather than inside gen-schema.
#
# Function of a NAMED dep (gen convention §8): the only dependency is gen-prelude's
# pure utility surface. No nixpkgs.lib anywhere under lib/ (purity invariant).
{
  prelude,
  identity,
  algebra,
}:
let
  core = import ./checkers.nix { inherit prelude identity algebra; };
  inherit (core)
    checkers
    mkChecker
    mkCompositeSealed
    mkIdentity
    completedType
    stampOk
    identityGuard
    comparisonSubject
    verifiersOf
    rewritesCheck
    witnessedCheck
    witnessRecord
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
  # also why the readers below never call `idOf`: `idOf` is the DEMAND for an identity,
  # and demanding one of a sealed checker is a refusal — so a reader that DECIDES must
  # dispatch on the tag instead of demanding.
  #
  #   minted     — an identity over a preimage total in the checker's distinguishing
  #                content; the digests decide.
  #   unmintable — no identity and no substitute; the decision compares the reified
  #                checker record.
  #   unmigrated — the migration window: no producer has stamped this checker, so its
  #                name is still all the decision has. This arm stays live until the
  #                producer lands, and while it is live the relation is byte-for-byte
  #                the shipped one — identity was then a pure function of `name`.
  identityOf =
    v:
    # a record whose `check` a wrapper rewrote keeps its base's `__mint`, which no longer states
    # its domain: it is compared, never minted (den-hoag-ydro3)
    if rewritesCheck v then
      { unmintable = v.name or "<unnamed>"; }
    else if v ? __mint && v.__mint ? minted then
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
      # constructors mint natively, and so do gen-merge's composites (`listOf`, `attrsOf`, `nullOr`,
      # `either`, `submodule`, `deriveType`), through this library's `mkIdentity`, under the
      # constructor names `gen-merge.<name>`.
      #
      # The consequence is deliberate: separately built foreign twins, and one leaf across two lib
      # instances, compare unequal. A record that lacks `__mint` AND `nestedTypes` (the
      # pre-migration population) falls through to the name-only branch below.
      { unmintable = v.name or "<unnamed>"; }
    else
      { unmigrated = v.name; };

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
  # Both operands minted: distinct marks decide `false` and equal marks are decided over the two
  # `__sealed` maps by gen-algebra's `sealedCollisionEq` — `true` when they are `==`, `false` when
  # every differing leaf is an inert declared subject (two registered constructions), and a refusal
  # by name otherwise (two separately written lambdas, which no `==` can tell apart from one).
  nameOf = v: if builtins.isString (v.name or null) then v.name else "<unnamed>";
  subjectOf = i: v: {
    name = if builtins.isString (v.name or null) then v.name else "<unnamed>";
    mark = i.minted;
    sealed = v.__sealed or { };
  };
  conservativeEq =
    a: b:
    let
      ia = identityOf a;
      ib = identityOf b;
    in
    if !(stampOk a) || !(stampOk b) then
      throw "gen-types: typeEq: `${
        nameOf (if stampOk a then b else a)
      }' is not the record its constructor completed: a `//` over a type keeps its identity while changing what that identity stands for; build the change through a constructor"
    else if ia ? minted && ib ? minted then
      ia.minted == ib.minted
      && algebra.sealedCollisionEq "gen-types: typeEq" (subjectOf ia a) (subjectOf ib b)
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
      mkCompositeSealed
      verifiersOf
      renderNode
      ;
    inherit (algebra) sealedMarker hasDeclaredSubject;
    inherit completedType;
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

  # ── the identity DEMAND (den-hoag-6orb8 A1) ──
  # `idOf t` is the one way to DEMAND a type's identity: its minted digest where the record has an
  # exact one, and a refusal BY NAME, catchably, where it has none. A record's fields are total data
  # and a partial operation is a function, so no field refuses when forced and `deepSeq` of any type
  # record is safe; this is where the refusal lives instead.
  #
  # ★ A PURE PROJECTION over the two cached total fields `__mint` and `__sealed`: it never re-mints,
  # so a repeated demand costs no `hashIdentity` (an idOf re-minting per call measured 86–5,026
  # thunks per demand, den-ag-design `reports/den-hoag-6orb8-id-perf-scout-v0.md`). Every producer
  # of a minted type states `__sealed`, so it is read directly; a minted record without one is
  # refused by name, never read as `{ }`.
  #
  # Deciding is not demanding: `typeEq` decides a type with no identity and never calls this.
  idOf =
    t:
    if !(builtins.isAttrs t && t ? __mint && builtins.isAttrs t.__mint) then
      throw "identity: ${
        if builtins.isAttrs t then "type '${nameOf t}'" else "a ${builtins.typeOf t}"
      } carries no `__mint`: it is no type record of this vocabulary, so it has no identity to demand"
    else if t.__mint ? minted then
      if !(t ? __sealed) then
        throw "identity: type '${nameOf t}' carries a mint and no `__sealed`: its producer states no sealed components, so its mark cannot be read as an identity"
      else if t.__sealed == { } then
        t.__mint.minted
      else
        throw "identity: type '${nameOf t}' has sealed component(s) ${
          builtins.concatStringsSep ", " (map (k: "'${k}'") (builtins.attrNames t.__sealed))
        } (a caller-supplied lambda, a registered construction, or a type with no minted identity), which its mark is blind to: it is decided by `typeEq` and has no identity to demand"
    else
      throw "identity: type '${nameOf t}' has no identity to demand: ${
        let
          u = t.__mint.unmintable or null;
        in
        if builtins.isAttrs u && builtins.isString (u.reason or null) then
          u.reason
        else if builtins.isString u then
          u
        else
          "its `__mint` is not minted"
      }";

  # ── the construction-payload reader ──
  # The ONE reader of `__payload` (lib/checkers.nix, `mkComposite`): it answers `{ ctor; args; }`
  # only where that payload is the PREIMAGE OF THE DIGEST THE RECORD CARRIES, and refuses by name,
  # catchably, everywhere else — a sealed checker, a foreign record, and a `//`-derived record
  # carrying its base's payload under a digest of its own. Re-minting ties the payload to the
  # digest by construction, so no producer's strip list is kept in step by hand; it invokes the
  # one minting authority and adds none. The answer is read-only and bears no identity: `__mint`
  # decides identity and `idOf` answers a demand for it.
  payloadOf =
    t:
    let
      p = t.__payload.minted;
    in
    if
      builtins.isAttrs t
      && t ? __mint
      && builtins.isAttrs t.__mint
      && t.__mint ? minted
      && !(rewritesCheck t)
      && t ? __payload
      && builtins.isAttrs t.__payload
      && t.__payload ? minted
      && builtins.isAttrs p
      && p ? ctor
      && p ? args
      && (t.__sealed or { }) == { }
      && identity.hashIdentity "type" [ "ctor" "args" ] (l: p.${l}) == t.__mint.minted
    then
      p
    else
      throw "gen-types: payloadOf: `${
        if builtins.isAttrs t && builtins.isString (t.name or null) then t.name else "<unnamed>"
      }' has no readable construction payload: ${
        if !(builtins.isAttrs t && t ? __mint && builtins.isAttrs t.__mint && t.__mint ? minted) then
          "its identity is not minted"
        else if rewritesCheck t then
          "a wrapper rewrote its `check', so the construction its `__mint' names is its base's, not its own"
        else if !(t ? __payload && builtins.isAttrs t.__payload && t.__payload ? minted) then
          "it carries no minted `__payload'"
        else if (t.__sealed or { }) != { } then
          "it carries sealed component(s), so its payload is not a total preimage"
        else
          "its `__payload' is not the preimage of its own digest"
      }";

  # ── the per-component identity, for a producer outside this library ──
  # `mkIdentity ctor members mkArgs sealed name` returns the identity fields every constructor here
  # carries (`__mint`, `__payload`, `__sealed`, and `__okAt` on a composite), so a type built
  # elsewhere (gen-schema's `refined`) is identified by the same construction and decided by the same
  # `typeEq`. See `mkIdentity` in `./checkers.nix`.
  inherit mkIdentity comparisonSubject;

  # ── the completion stamp's reader, for a boundary that rebuilds a type record ──
  # `stampOk t` holds when `t` is the record its constructor (or the last boundary) completed, and
  # fails on a `//` copy. gen-merge's protocol boundary reads it on import and re-ties the stamp to the
  # record it completes (see `completedType` in `./checkers.nix`).
  inherit stampOk;

  # ── the type-identity guard, for a producer outside this library ──
  # A construct that mints over a member's `__mint` must step the same index or it reopens the
  # blackhole a self-referential type closes (see `identityGuard` in `./checkers.nix`); gen-schema's
  # `refined` is the one such producer. Exported so the bound and its refusal stay single-sourced.
  inherit identityGuard;

  # ── the check-witness protocol (den-hoag-ydro3, OQ-A arm ii) ──
  inherit rewritesCheck witnessedCheck witnessRecord;
}
