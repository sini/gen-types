# gen-types: the refusal renderer `toPretty` is shallow, budgeted and total. It reads the value a
# door hands it and never a member, so a member that throws, errors, cycles or nests cannot abort
# or replace a refusal, and the rendered value stays within `renderBudget` + 34 bytes.
{ genTypes, ... }:
let
  t = genTypes;
  cyclic =
    let
      s = {
        self = s;
        tag = "c";
      };
    in
    s;
  cyc32 =
    let
      l = builtins.genList (_: l) 32;
    in
    l;
  cyc16 =
    let
      l = builtins.genList (_: l) 16;
    in
    l;
  nest = n: v: builtins.foldl' (acc: _: { a = acc; }) v (builtins.genList (x: x) n);
  deep = builtins.foldl' (acc: _: [ acc ]) 0 (builtins.genList (x: x) 20000);
  hugeSet = builtins.listToAttrs (
    builtins.genList (i: {
      name = "k${toString i}";
      value = i;
    }) 20000
  );
  hugeStr = builtins.concatStringsSep "" (builtins.genList (_: "x") 200000);
  pre = "expected type 'int' but value ";
in
{
  # members are never forced
  flake.tests.types-render.test-cyclic-set-renders-shallow = {
    expr = t.int.verify cyclic;
    expected = "${pre}{ self = …; tag = …; } is of type 'set'";
  };
  flake.tests.types-render.test-cyclic-refusal-is-catchable = {
    expr = (builtins.tryEval (t.int.check cyclic null)).success;
    expected = false;
  };
  flake.tests.types-render.test-deep-list-renders-shallow = {
    expr = t.int.verify deep;
    expected = "${pre}[ … (1 element) ] is of type 'list'";
  };
  flake.tests.types-render.test-throwing-element-not-forced = {
    expr = t.int.verify [
      "a"
      (throw "x")
    ];
    expected = "${pre}[ … (2 elements) ] is of type 'list'";
  };
  flake.tests.types-render.test-evaluator-error-element-not-forced = {
    expr = t.int.verify [
      "a"
      (1 + "a")
    ];
    expected = "${pre}[ … (2 elements) ] is of type 'list'";
  };
  flake.tests.types-render.test-evaluator-error-field-not-forced = {
    expr = t.int.verify { a = 1 + "a"; };
    expected = "${pre}{ a = …; } is of type 'set'";
  };
  # no member is read to classify the value (a derivation test reads `type`)
  flake.tests.types-render.test-type-field-not-forced = {
    expr = t.int.verify { type = 1 + "a"; };
    expected = "${pre}{ type = …; } is of type 'set'";
  };
  flake.tests.types-render.test-type-field-at-depth-not-forced = {
    expr = t.int.verify (nest 6 { type = 1 + "a"; });
    expected = "${pre}{ a = …; } is of type 'set'";
  };
  # the global byte budget
  flake.tests.types-render.test-width-32-cycle-returns-bounded = {
    expr = t.int.verify cyc32;
    expected = "${pre}[ … (32 elements) ] is of type 'list'";
  };
  flake.tests.types-render.test-huge-set-fills-budget = {
    expr = t.int.verify hugeSet;
    expected = "${pre}{ k0 = …; k1 = …; k10 = …; k100 = …; k1000 = …; k10000 = …; k10001 = …; k10002 = …; k10003 = …; k10004 = …; k10005 = …; k10006 = …; k10007 = …; k10008 = …; k10009 = …; k1001 = …; k10010 = …; k10011 = …; k10012 = …; … (19981 more) } is of type 'set'";
  };
  flake.tests.types-render.test-huge-string-cut-at-budget = {
    expr = builtins.stringLength (t.int.verify hugeStr);
    expected = 311;
  };
  # the renderer reached through union: a refusing member's message renders the value shallowly,
  # so the member that accepts is reached
  flake.tests.types-render.test-union-accepts-without-rendering = {
    expr =
      (t.union [
        t.int
        t.attrs
      ]).verify
        { a = 1 + "a"; };
    expected = null;
  };
  flake.tests.types-render.test-union-accepts-cycle-without-rendering = {
    expr =
      (t.union [
        t.int
        t.list
      ]).verify
        cyc16;
    expected = null;
  };
  # controls, same run
  flake.tests.types-render.test-union-still-refuses = {
    expr =
      (t.union [
        t.int
        t.attrs
      ]).verify
        "s";
    expected = "expected type 'union<int,attrs>' but value \"s\" is of type 'string'";
  };
  flake.tests.types-render.test-scalar-renders-whole = {
    expr = t.int.verify "s";
    expected = "${pre}\"s\" is of type 'string'";
  };
}
