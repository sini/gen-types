# gen-types: the check-witness protocol (den-hoag-ydro3, OQ-A arm (ii)), and a composite that
# carries the `check` a wrapper stated over its member. gen-types owns the protocol, so the witness
# here is built by its own `witnessedCheck`, never stated by hand.
#
# RED with the chokepoint reverted (members read through a bare `t.verify`, `idOf`, `identityOf`
# and `payloadOf` not asking `rewritesCheck`): `rewrittenRefuses5`, `structRefuses5` and
# `unionRefuses5` read V, `listOfEq` and `leafEq` read `true`, `mintTag` reads `minted`, and
# `payloadRefused` reads `false`. The controls read the same on both trees.
{ genTypes, lib, ... }:
let
  t = genTypes;
  w = t.witnessedCheck (x: x > 0);
  rec0 = {
    name = "r";
  }
  // w;
  # a producer's record over a gen-types leaf: its domain stated as `verify` and as a witnessed `check`
  own = t.int // t.witnessedCheck (x: t.int.verify x == null);
  rewritten = own // {
    check = x: own.check x && x < 3;
  };
  v = ty: x: if ty.verify x == null then "V" else "R";
  ref = {
    check = _: true;
    message = "m";
  };
in
{
  flake.tests.types-added-check.test-protocol = {
    expr = {
      own = t.rewritesCheck rec0;
      applies = rec0.check 3;
      refuses = rec0.check (-1);
      overwrite = t.rewritesCheck (rec0 // { check = _: true; });
      reselect = t.rewritesCheck (rec0 // { inherit (rec0) check; });
      unrelated = t.rewritesCheck (rec0 // { foo = 1; });
      noWitness = t.rewritesCheck { check = _: true; };
      bare = t.rewritesCheck { };
      nonAttrs = t.rewritesCheck 3;
      checker = t.rewritesCheck t.int;
      isFunction = lib.isFunction rec0.check;
      builtinsIsFunction = builtins.isFunction rec0.check;
    };
    expected = {
      own = false;
      applies = true;
      refuses = false;
      overwrite = true;
      reselect = false;
      unrelated = false;
      noWitness = false;
      bare = false;
      nonAttrs = false;
      checker = false;
      isFunction = true;
      builtinsIsFunction = false;
    };
  };

  # the published surface, pinned: the protocol adds exactly `rewritesCheck` and `witnessedCheck`
  flake.tests.types-added-check.test-lib-surface = {
    expr = builtins.attrNames t;
    expected = [
      "any"
      "attrs"
      "attrsOf"
      "bool"
      "conservativeEq"
      "defaultOnError"
      "derivation"
      "enum"
      "float"
      "formatErrors"
      "function"
      "identityGuard"
      "int"
      "intersection"
      "list"
      "listOf"
      "mkValidator"
      "never"
      "null"
      "number"
      "option"
      "optionalAttr"
      "path"
      "pathLike"
      "payloadOf"
      "refined"
      "refinements"
      "rewritesCheck"
      "runValidators"
      "str"
      "strict"
      "string"
      "struct"
      "tuple"
      "typeEq"
      "typedef"
      "typedef'"
      "union"
      "witnessedCheck"
    ];
  };

  # the README's example, verbatim in meaning
  flake.tests.types-added-check.test-protocol-over-a-checker = {
    expr =
      let
        own = t.int // t.witnessedCheck (x: x > 0);
      in
      [
        (t.rewritesCheck own)
        (t.rewritesCheck (own // { check = _: true; }))
        (t.rewritesCheck (own // { inherit (own) check; }))
        (t.rewritesCheck t.int)
      ];
    expected = [
      false
      true
      false
      false
    ];
  };

  flake.tests.types-added-check.test-composite-carries-added-check = {
    expr = {
      ownServes5 = v (t.refined own [ ref ]) 5;
      rewrittenRefuses5 = v (t.refined rewritten [ ref ]) 5;
      rewrittenServes2 = v (t.refined rewritten [ ref ]) 2;
      structRefuses5 = v (t.struct "s" { a = rewritten; }) { a = 5; };
      structServes2 = v (t.struct "s" { a = rewritten; }) { a = 2; };
      unionRefuses5 = v (t.union [ rewritten ]) 5;
      listOfEq = t.typeEq (t.listOf own) (t.listOf rewritten);
      listOfSelf = t.typeEq (t.listOf own) (t.listOf own);
      leafEq = t.typeEq own rewritten;
      leafSelf = t.typeEq rewritten rewritten;
      mintTag = builtins.attrNames (t.listOf rewritten).__mint;
      mintTagOwn = builtins.attrNames (t.listOf own).__mint;
      payloadRefused = !(builtins.tryEval (t.payloadOf rewritten)).success;
      payloadOwn = (t.payloadOf own).ctor;
    };
    expected = {
      ownServes5 = "V";
      rewrittenRefuses5 = "R";
      rewrittenServes2 = "V";
      structRefuses5 = "R";
      structServes2 = "V";
      unionRefuses5 = "R";
      listOfEq = false;
      listOfSelf = true;
      leafEq = false;
      leafSelf = true;
      mintTag = [ "unmintable" ];
      mintTagOwn = [ "minted" ];
      payloadRefused = true;
      payloadOwn = "prim";
    };
  };
}
