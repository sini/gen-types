# gen-types: `typedef`'s options-first `merge` (den-hoag-6orb8 U3) and G4's rendering. This library
# CARRIES `merge` as a component of the type's identity and interprets none of it (gen-merge folds
# with it, ci there); the cells read the door, the carried field and the identity. Names are invented
# (ADR-0035).
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
  isInt = v: builtins.isInt v;
  sum = _loc: defs: builtins.foldl' (a: d: a + d.value) 0 defs;
  sum' = _loc: defs: builtins.foldl' (a: d: a + d.value) 0 defs;
  tallies = {
    revision = "r1";
    members.sum =
      _a: _loc: defs:
      builtins.foldl' (a: d: a + d.value) 0 defs;
  };
  sumOf = args: algebra.mkIntensional identity.hashIdentity tallies "sum" args;
  tally = m: t.typedef { merge = m; } "tally" isInt;
  defs = [
    {
      file = "a";
      value = 2;
    }
    {
      file = "b";
      value = 3;
    }
  ];
in
{
  flake.tests.types-typedef-merge = {
    # U3-m1 at this library: the record carries the caller's fold, which folds as written
    test-the-merge-is-carried-and-folds = {
      expr = (tally sum).merge [ "o" ] defs;
      expected = 5;
    };
    test-no-merge-carries-no-merge-field = {
      expr = (t.typedef { } "tally" isInt) ? merge;
      expected = false;
    };
    test-a-registered-merge-folds = {
      expr = (tally (sumOf { })).merge [ "o" ] defs;
      expected = 5;
    };
    # the door: options first and closed; the positional form, an unknown option and a non-function
    # merge refuse at construction, catchably (messages: ../tests-error.nix)
    test-the-door-refuses-by-construction = {
      expr = {
        positional = unbuilt (t.typedef "tally" isInt);
        unknown = unbuilt (t.typedef { mrege = sum; } "tally" isInt);
        integerMerge = unbuilt (tally 3);
        recordMerge = unbuilt (tally {
          lo = 1;
        });
        control = (tally sum).verify 4;
      };
      expected = {
        positional = true;
        unknown = true;
        integerMerge = true;
        recordMerge = true;
        control = null;
      };
    };
    # `merge` is a component like the predicate: one binding shared is one type, two separately
    # written merges refuse, a registered one is compared, and an absent one is the inert `null`
    test-merge-is-a-component-of-identity = {
      expr = {
        oneBinding = t.typeEq (tally sum) (tally sum);
        twoLambdas = refused (t.typeEq (tally sum) (tally sum'));
        registeredTwins = t.typeEq (tally (sumOf { })) (tally (sumOf { }));
        registeredOther = t.typeEq (tally (sumOf { })) (
          tally (sumOf {
            k = 1;
          })
        );
        withVsWithout = t.typeEq (tally sum) (t.typedef { } "tally" isInt);
        marksApart = (tally sum).__mint.minted != (t.typedef { } "tally" isInt).__mint.minted;
        sealedAtMerge = (tally sum).__sealed ? merge;
        noMergeSealsNone = (t.typedef { } "tally" isInt).__sealed ? merge;
        stamp = t.stampOk (tally sum);
      };
      expected = {
        oneBinding = true;
        twoLambdas = true;
        registeredTwins = true;
        registeredOther = false;
        withVsWithout = false;
        marksApart = true;
        sealedAtMerge = true;
        noMergeSealsNone = false;
        stamp = true;
      };
    };
  };

  # G4: the documentation renders a `refined`'s contracts beside its base, and a `struct` its members
  flake.tests.types-render-docs = {
    test-refined-renders-its-contracts = {
      expr =
        (t.refined t.int [
          t.refinements.positive
          t.refinements.tcpPort
        ]).description;
      expected = "int (must be positive; must be a valid TCP port (1-65535))";
    };
    test-struct-carries-a-description = {
      expr = [
        (t.struct "point" {
          x = t.int;
          y = t.str;
        }).description
        (
          let
            s = t.struct "s" { n = t.optionalAttr s; };
          in
          s.description
        )
      ];
      expected = [
        "struct 'point' { x: int; y: string }"
        "struct 's' { n: optionalAttr<s> }"
      ];
    };
  };
}
