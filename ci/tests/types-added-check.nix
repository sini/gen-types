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

  # ★ R: A RECORD RE-TIED OVER A REWRITTEN CHECK IS COMPARED, NOT DECIDED BY ITS BASE'S MARK. A boundary
  # completes a record over `int` with a witnessed `check` and ties its stamp (`typeWitness` declared, as
  # gen-merge's doors do); a wrapper then rewrites the `check` and the boundary re-ties the stamp over the
  # rewrite. The stamp holds, so the completion witness does not decide it: the declared check witness
  # does, and the record keeps `int`'s mark only as a bucket label. RED with the `checks` half of the
  # declaration unread (`retiedIsBase` reads `true`: the two marks are one digest). The twins decide
  # `true`, so a relation separating everything cannot pass.
  flake.tests.types-added-check.test-a-record-retied-over-a-rewritten-check-is-compared =
    let
      tie =
        r:
        let
          s = r // {
            __typeSelf = _: s;
            __witness = t.typeWitness;
          };
        in
        s;
      completed = tie (t.int // t.witnessedCheck (x: t.int.verify x == null));
      # nixpkgs' `addCheck`, as its v1 form writes it: every field copied, `check` rewritten
      addCheck = elemType: check: elemType // { check = x: elemType.check x && check x; };
      retied = tie (addCheck completed (n: n < 3));
    in
    {
      expr = {
        stampHolds = t.stampOk retied;
        rewritten = t.rewritesCheck retied;
        sameMark = retied.__mint == completed.__mint;
        retiedIsBase = t.typeEq completed retied;
        completedIsItself = t.typeEq completed completed;
        retiedIsItself = t.typeEq retied retied;
      };
      expected = {
        stampHolds = true;
        rewritten = true;
        sameMark = true;
        retiedIsBase = false;
        completedIsItself = true;
        retiedIsItself = true;
      };
    };

  # the published surface, pinned: the protocol adds exactly `rewritesCheck`, `witnessedCheck` and
  # `witnessRecord`
  flake.tests.types-added-check.test-lib-surface = {
    expr = builtins.attrNames t;
    expected = [
      "any"
      "attrs"
      "attrsOf"
      "bool"
      "checkedAttrsOf"
      "checkedListOf"
      "checkedOption"
      "comparisonSubject"
      "conservativeEq"
      "defaultOnError"
      "derivation"
      "enum"
      "float"
      "formatErrors"
      "function"
      "idOf"
      "identityGuard"
      "int"
      "intersection"
      "list"
      "listOf"
      "mkIdentity"
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
      "stampOk"
      "str"
      "strict"
      "string"
      "struct"
      "tuple"
      "typeEq"
      "typeWitness"
      "typedef"
      "typedef'"
      "union"
      "witnessRecord"
      "witnessedCheck"
    ];
  };

  # `witnessRecord`: the one record `witnessedCheck` publishes twice. A caller publishing it under
  # both fields itself builds `witnessedCheck`'s layout, and the test reads that pair as it reads
  # `witnessedCheck`'s. RED if the record's shape moves away from the pair's.
  flake.tests.types-added-check.test-witness-record = {
    expr =
      let
        r = t.witnessRecord (x: x > 0);
        spelled = t.int // {
          check = r;
          _checkWitness = r;
        };
        built = t.witnessedCheck (x: x > 0);
      in
      {
        fields = builtins.attrNames built;
        recordShape = builtins.attrNames r == builtins.attrNames built.check;
        applies = r 3;
        refuses = r (-1);
        isFunction = lib.isFunction r;
        builtinsIsFunction = builtins.isFunction r;
        own = t.rewritesCheck spelled;
        overwrite = t.rewritesCheck (spelled // { check = _: true; });
        reselect = t.rewritesCheck (spelled // { inherit (spelled) check; });
      };
    expected = {
      fields = [
        "_checkWitness"
        "check"
      ];
      recordShape = true;
      applies = true;
      refuses = false;
      isFunction = true;
      builtinsIsFunction = false;
      own = false;
      overwrite = true;
      reselect = false;
    };
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
      # `own` is a `//` copy, so it enters `listOf` sealed beside `rewritten` (den-hoag-6d5r3): one mark,
      # two sealed subjects, refused by name
      listOfEq = !(builtins.tryEval (t.typeEq (t.checkedListOf own) (t.checkedListOf rewritten))).success;
      listOfSelf = t.typeEq (t.checkedListOf own) (t.checkedListOf own);
      # `own` and `rewritten` are `//` copies of `int`, so `typeEq` refuses them by name (the
      # completion stamp); `listOf` over them completes a record of its own and decides
      leafEq = !(builtins.tryEval (t.typeEq own rewritten)).success;
      leafSelf = !(builtins.tryEval (t.typeEq rewritten rewritten)).success;
      mintTag = builtins.attrNames (t.checkedListOf rewritten).__mint;
      mintTagOwn = builtins.attrNames (t.checkedListOf own).__mint;
      # the rewritten member is a sealed component, whatever its base's mint says
      sealedRewritten = builtins.attrNames (t.checkedListOf rewritten).__sealed;
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
      listOfEq = true;
      listOfSelf = true;
      leafEq = true;
      leafSelf = true;
      mintTag = [ "minted" ];
      sealedRewritten = [ "members.0" ];
      mintTagOwn = [ "minted" ];
      payloadRefused = true;
      payloadOwn = "prim";
    };
  };
}
