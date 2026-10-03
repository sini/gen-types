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
  # Takes the identity core (name/verify/check/__name/__nameWithin/__id/__mint).
  #
  # ★★ A REFINED TYPE'S DISTINGUISHING CONTENT IS `base ⊕ predicate`, AND THE NAME CARRIES ONLY THE
  # BASE. `refined<int>` says nothing about which predicates a value must satisfy, so two different
  # refinements of one base compared EQUAL under a name-only identity — measured, `refined int
  # positive` == `refined int tcpPort`. The base is mint-admissible and enters as its own identity;
  # the predicates are the problem, and they are the ecosystem's first migration case.
  #
  # ★★★ SO EACH PREDICATE IS A SEALED COMPONENT, PER ADR-0034's PER-COMPONENT READING. A refinement
  # is `{ check; message; }` with `check` a caller lambda or a registered construction (gen-algebra
  # `mkIntensional`), and no preimage over a closure can be total. The type mints over its
  # constructor, its base's tag and each refinement with `sealedMarker` in place of its `check`; the
  # checks are carried in `__sealed`, a lambda in its own slot (so a stock refinement such as
  # `positive` shared by two types decides `true`) and a registered construction by its declared
  # subject (so two constructions of one term decide `true`). `typeEq` decides over the mark and
  # those subjects, and demanding `__id` refuses by name.
  refined =
    {
      mkCompositeSealed,
      verifiersOf,
      renderNode,
      sealedMarker,
      hasDeclaredSubject,
      completedType,
    }:
    base: refinements:
    let
      refs = normalize refinements;
      # the base renders as a member does, within the budget and by its own renderer where it has
      # one, so a base with none is bounded too and a non-string base name refuses by name
      render = renderNode "refined" "refined<" "" ">" [ base ];
      baseVerify = builtins.head (verifiersOf "refined" [ base ]);
    in
    completedType (
      mkCompositeSealed "refined" [ base ]
        (tags: {
          base = builtins.head tags;
          # a refinement's `check` is sealed; one with no `check` is inert and enters whole, and one
          # that is not a record is sealed whole
          refinements = map (
            r:
            if !(builtins.isAttrs r) then
              sealedMarker
            else if r ? check then
              r // { check = sealedMarker; }
            else
              r
          ) refs;
        })
        (builtins.concatLists (
          builtins.genList (
            i:
            let
              r = elemAt refs i;
              path = [
                "refinements"
                (toString i)
              ];
            in
            if !(builtins.isAttrs r) then
              [
                {
                  inherit path;
                  value = r;
                }
              ]
            else if !(r ? check) then
              [ ]
            else
              [
                {
                  inherit path;
                  # a slice keeps the check's slot, where a selection would be a fresh thunk
                  value = if hasDeclaredSubject r.check then r.check else builtins.intersectAttrs { check = null; } r;
                }
              ]
          ) (length refs)
        ))
        render
        (
          v:
          let
            baseErr = builtins.seq baseVerify (baseVerify v);
          in
          if baseErr != null then baseErr else firstFailingRefinement refs v
        )
      // {
        # introspection parity with the old __schema.refinements surface
        __refinements = refs;
      }
    );

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
