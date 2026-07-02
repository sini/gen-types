# Refinement contracts, folded onto the pure checker (was lib/refined.nix, which
# hung predicates off nixpkgs option types via a `__schema` attr). Here a refined
# type is a base CHECKER plus a list of predicate contracts — § Findler 2002
# boundaries, co-located with the base in the style of § Rondon 2008 liquid types.
#
# A refinement is a record { check = value -> bool; message; }. `refined base refs`
# runs the base first (so predicates only ever see well-typed values) then, on the
# happy path, confirms every predicate in a single pass; the offending message is
# located only when a predicate is known to fail.
{ prelude }:
let
  inherit (prelude)
    all
    elemAt
    isList
    length
    ;

  normalize = r: if isList r then r else [ r ];

  # Predicate-first-failure with the same single-pass/rescan discipline as the
  # collection combinators in checkers.nix.
  firstFailingRefinement =
    refs: v:
    if all (r: r.check v) refs then
      null
    else
      let
        recur =
          i:
          let
            r = elemAt refs i;
          in
          if r.check v then recur (i + 1) else r.message;
      in
      recur 0;
in
{
  # refined : baseChecker -> (refinement | [refinement]) -> checker
  # Depends on the checker set for typedef' (name/verify/check/__name/__id).
  refined =
    checkers: base: refinements:
    let
      refs = normalize refinements;
      name = "refined<${base.name}>";
    in
    checkers.typedef' name (
      v:
      let
        baseErr = base.verify v;
      in
      if baseErr != null then baseErr else firstFailingRefinement refs v
    )
    // {
      # introspection parity with the old __schema.refinements surface
      __refinements = refs;
    };

  # The stock predicate library (behaviour-identical to lib/refined.nix).
  refinements = {
    tcpPort = {
      check = self: self > 0 && self < 65536;
      message = "must be a valid TCP port (1-65535)";
    };
    nonEmpty = {
      check = self: self != "";
      message = "must not be empty";
    };
    positive = {
      check = self: self > 0;
      message = "must be positive";
    };
  };
}
