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
  # Takes the identity core (name/verify/check/__name/__id/__mint).
  #
  # ★★ A REFINED TYPE'S DISTINGUISHING CONTENT IS `base ⊕ predicate`, AND THE NAME CARRIES ONLY THE
  # BASE. `refined<int>` says nothing about which predicates a value must satisfy, so two different
  # refinements of one base compared EQUAL under a name-only identity — measured, `refined int
  # positive` == `refined int tcpPort`. The base is mint-admissible and enters as its own identity;
  # the predicates are the problem, and they are the ecosystem's first migration case.
  #
  # ★★★ SO THIS FAMILY IS SEALED TODAY, AND THAT IS THE ANSWER RATHER THAN A GAP. A refinement is
  # `{ check = value -> bool; message; }` — an arbitrary CALLER-SUPPLIED lambda, `normalize` above
  # accepting whatever the caller passes — and no preimage over a closure can be total. ADR-0034
  # takes the per-component reading: where a component's distinguishing content is a caller lambda,
  # its collapse is replaced by a REFUSAL and never by a structural identity. So `typeEq` decides
  # about two refined types by comparing their reified records, which separates them, and demanding
  # `__id` of one refuses by name. That is strictly better than the silent merge it replaces and it
  # is NOT k1uv's resolution for this family — the resolution is the migration below.
  #
  # ★ WHAT WOULD HAVE TO CHANGE, written at the declaration as the burden asymmetry requires: the
  # predicate stops being a lambda. A refinement becomes a first-order term `{ pred; args; message; }`
  # whose `check` the substrate DERIVES from `(pred, args)` against a registry of predicate
  # builders; then both components are mint-admissible and this constructor mints over
  # `{ base = <base's identity>; refinements = [ {pred, args} … ] }` with no other edit here. Two
  # things block it and neither is this file's to decide: WHICH first-order vocabulary, given that
  # gen-schema carries a second `refined` implementation and the two must share one rather than
  # ship the vendoring defect one level up; and the shipped callers that pass inline lambdas today.
  refined =
    { mkChecker, idOf }:
    base: refinements:
    let
      refs = normalize refinements;
      name = "refined<${base.name}>";
    in
    mkChecker "refined"
      {
        base = idOf base;
        refinements = refs;
      }
      name
      (
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
