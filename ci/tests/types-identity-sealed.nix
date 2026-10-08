# gen-types: the per-component identity of a type with a SEALED component (den-hoag-6orb8 U1). A
# caller's predicate, a registered construction (gen-algebra `mkIntensional`) and a member with no
# minted identity are sealed components: the type mints over the rest and carries their subjects in
# `__sealed`, and `typeEq` decides over both. Names are invented (ADR-0035).
{
  genTypes,
  algebra,
  identity,
  ...
}:
let
  t = genTypes;
  refused = e: !(builtins.tryEval (builtins.deepSeq e e)).success;
  # built at all: WHNF only, so a refusal at construction is told from a value that merely holds one
  unbuilt = e: !(builtins.tryEval (builtins.seq e true)).success;
  basting = {
    revision = "r1";
    members.stitch = a: v: builtins.isInt v && v >= a.lo && v <= a.hi;
  };
  basting2 = basting // {
    revision = "r2";
  };
  its = reg: args: algebra.mkIntensional identity.hashIdentity reg "stitch" args;
  r1 = its basting {
    lo = 1;
    hi = 9;
  };
  r1' = its basting {
    lo = 1;
    hi = 9;
  };
  r9 = its basting {
    lo = 1;
    hi = 10;
  };
  rr2 = its basting2 {
    lo = 1;
    hi = 9;
  };
  even = v: builtins.isInt v && builtins.bitAnd v 1 == 0;
  even' = v: builtins.isInt v && builtins.bitAnd v 1 == 0;
  td = t.typedef "stitched";
  rf =
    c:
    t.refined t.int {
      check = c;
      message = "range";
    };
in
{
  # Two constructions of one registered term are ONE type; a different argument or revision is
  # another, decided `false` (the evidence clause), never refused. The mark is blind to the term.
  flake.tests.types-identity-sealed.test-registered-predicate-decides-by-its-subject = {
    expr = {
      twins = t.typeEq (td r1) (td r1');
      different = t.typeEq (td r1) (td r9);
      otherRevision = t.typeEq (td r1) (td rr2);
      markBlindToTerm = (td r1).__mint.minted == (td r9).__mint.minted;
      refinedTwins = t.typeEq (rf r1) (rf r1');
      refinedDifferent = t.typeEq (rf r1) (rf r9);
      checks = [
        ((td r1).verify 5)
        ((td r1).verify 50 != null)
      ];
    };
    expected = {
      twins = true;
      different = false;
      otherRevision = false;
      markBlindToTerm = true;
      refinedTwins = true;
      refinedDifferent = false;
      checks = [
        null
        true
      ];
    };
  };

  # A caller lambda is sealed in its own slot: one binding is one type, however many times it is
  # declared; two separately written lambdas are refused by name, because `==` cannot tell them
  # from one (ADR-0034: a sealed component's collapse is replaced by a refusal).
  flake.tests.types-identity-sealed.test-caller-lambda-is-sealed-in-its-slot = {
    expr = {
      oneBinding =
        let
          x = t.typedef "even" even;
        in
        t.typeEq x x;
      sharedPredicate = t.typeEq (t.typedef "even" even) (t.typedef "even" even);
      twoLambdas = refused (t.typeEq (t.typedef "even" even) (t.typedef "even" even'));
      otherName = t.typeEq (t.typedef "even" even) (t.typedef "odd" even);
      # `typedef` and `typedef'` over one function are two constructors
      predicateVsVerifier = t.typeEq (t.typedef "even" even) (t.typedef' "even" even);
    };
    expected = {
      oneBinding = true;
      sharedPredicate = true;
      twoLambdas = true;
      otherName = false;
      predicateVsVerifier = false;
    };
  };

  # PROPAGATION: a composite over a member that seals something carries the member's `__sealed`
  # under the member's path, so `listOf (typedef R1)` and `listOf (typedef R9)` share a mark and
  # still decide `false`; twins decide `true`.
  flake.tests.types-identity-sealed.test-sealed-subjects-propagate-through-composites = {
    expr = {
      markShared = (t.checkedListOf (td r1)).__mint.minted == (t.checkedListOf (td r9)).__mint.minted;
      different = t.typeEq (t.checkedListOf (td r1)) (t.checkedListOf (td r9));
      twins = t.typeEq (t.checkedListOf (td r1)) (t.checkedListOf (td r1'));
      nested = t.typeEq (t.checkedAttrsOf (t.checkedListOf (td r1))) (
        t.checkedAttrsOf (t.checkedListOf (td r9))
      );
    };
    expected = {
      markShared = true;
      different = false;
      twins = true;
      nested = false;
    };
  };

  # THE CHECK-WITNESS PROTOCOL DECIDES A MEMBER'S TAG: a member whose `check` a wrapper rewrote enters
  # sealed, never by its base's mint, so `refined int` and `refined (addCheck int odd)` over one term
  # mint apart and decide `false` (C6, the base collapse); a minted base is the control.
  flake.tests.types-identity-sealed.test-rewritten-member-enters-sealed = {
    expr =
      let
        oddBase = t.int // {
          check = v: builtins.isInt v && builtins.bitAnd v 1 == 1;
          _checkWitness = t.int.check or null;
        };
      in
      {
        mintsDiffer =
          (rf r1).__mint.minted != (t.refined oddBase {
            check = r1;
            message = "range";
          }).__mint.minted;
        decides = t.typeEq (rf r1) (
          t.refined oddBase {
            check = r1;
            message = "range";
          }
        );
        controlBaseStr = t.typeEq (rf r1) (
          t.refined t.str {
            check = r1;
            message = "range";
          }
        );
      };
    expected = {
      mintsDiffer = true;
      decides = false;
      controlBaseStr = false;
    };
  };

  # A type with a sealed component has a mark and no identity to DEMAND: `idOf` refuses by name and
  # `payloadOf` refuses its payload, while the minted control answers both.
  flake.tests.types-identity-sealed.test-a-mark-beside-sealed-components-is-no-identity = {
    expr = {
      id = refused (t.idOf (td r1));
      payload = refused (t.payloadOf (td r1));
      controlId = builtins.isString (t.idOf (t.checkedListOf t.int));
      controlPayload = (t.payloadOf (t.checkedListOf t.int)).ctor;
    };
    expected = {
      id = true;
      payload = true;
      controlId = true;
      controlPayload = "listOf";
    };
  };

  # The door takes a function or a registered construction and nothing else, refused by name and
  # catchably when the type is built (the message is pinned in `../tests-error.nix`).
  flake.tests.types-identity-sealed.test-predicate-door-refuses-other-forms = {
    expr = {
      integer = unbuilt (t.typedef "tally" 3);
      record = unbuilt (t.typedef "tally" { lo = 1; });
      verifierInteger = unbuilt (t.typedef' "tally" 3);
      controlFunctor = (t.typedef "tally" { __functor = _: v: builtins.isInt v; }).verify 1;
    };
    expected = {
      integer = true;
      record = true;
      verifierInteger = true;
      controlFunctor = null;
    };
  };
}
