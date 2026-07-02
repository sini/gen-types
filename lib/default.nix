# gen-types — pure, clean-room, MIT structural type CHECKER for the gen ecosystem.
#
# This is the CHECKING half of a pure-Nix module system: it answers "does this value
# inhabit this type?" and nothing else. A downstream byte-mode MERGE engine (gen-merge)
# sits ABOVE gen-types and consumes these checkers to verify LEAVES — it owns all
# definition merging, priority, and fixpoint. gen-types carries NO merge/priority
# notion whatsoever; the type value is a pure predicate boundary.
#
# The handoff contract is the checker record itself — { name; verify; check; __name;
# __id } — so gen-merge calls `t.verify` on a merged leaf value (null = ok, else a
# blame string) and `t.__id` to decide whether two option declarations carry the same
# type. gen-types is a self-contained LEAF: it must import WITHOUT any registry above
# it, which is why it lives in its own flake rather than inside gen-schema.
#
# Function of a NAMED dep (gen convention §8): the only dependency is gen-prelude's
# pure utility surface. No nixpkgs.lib anywhere under lib/ (purity invariant).
{ prelude }:
let
  checkers = import ./checkers.nix { inherit prelude; };
  refinedLib = import ./refined.nix { inherit prelude; };
  validateLib = import ./validate.nix { inherit prelude; };
  strictLib = import ./strict.nix { inherit prelude; };
in
# The checker constructor set IS the public surface; the fold-ins (refined/strict/
# validators) and the identity helpers ride alongside it.
checkers
// {
  # refinement contracts
  refined = refinedLib.refined checkers;
  inherit (refinedLib) refinements;

  # closed-world unknown-key rejection
  strict = strictLib.strict checkers;

  # validator base (predicate contracts over a kind's instances)
  inherit (validateLib)
    mkValidator
    runValidators
    formatErrors
    defaultOnError
    ;

  # ── intensional identity (Palmer-style, name-derived) ──
  # Two checkers denote the same type iff their names agree; __id is the sha256
  # content address of that name (same discipline as gen-schema's id_hash). This
  # is the deliberate name-only ceiling — no closure/structural comparison.
  typeEq = a: b: a.__id == b.__id;
  intensionalEq = a: b: a.__id == b.__id;
}
