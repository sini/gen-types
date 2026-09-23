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
    attrValues
    elem
    any
    map
    ;
  core = import ./checkers.nix { inherit prelude identity; };
  inherit (core)
    checkers
    mkChecker
    idOf
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
  # and the walk never touches `.check`/`.merge`/`.functor.type` (nixpkgs' one self-referential
  # field) at any depth — only `.name` and `.nestedTypes`.
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

  mintForeign =
    t:
    let
      children = attrValues (t.nestedTypes or { });
      mintedChildren = map mintForeign children;
    in
    if children == [ ] then
      if elem t.name foreignLeafRegistry then
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
      let
        m = mintForeign v;
      in
      if m ? minted then { inherit (m) minted; } else { unmintable = m.sealed; }
    else
      { unmigrated = v.name; };

  # The comparison SUBJECT for the sealed arm: the reified record MINUS `__id`, and
  # minus nothing else.
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
  comparisonSubject = v: removeAttrs v [ "__id" ];

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
      mkChecker
      idOf
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
}
