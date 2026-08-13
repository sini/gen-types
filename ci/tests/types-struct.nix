# gen-types: struct — totality, unknown-key policy, custom invariants, nesting,
# optionalAttr members, and error-context threading.
{ genTypes, ... }:
let
  t = genTypes;

  point = t.struct "point" {
    x = t.int;
    y = t.int;
  };

  inv = v: if (v.x or 0) + (v.y or 0) == 3 then null else "sum must be 3";

  # The composing contract as an identity: chaining deltas equals one merged delta.
  law2 =
    a: b: v:
    ((point.override a).override b).verify v == (point.override (a // b)).verify v;
  law3 =
    a: b: c: v:
    (((point.override a).override b).override c).verify v == (point.override (a // b // c)).verify v;
in
{
  flake.tests.types-struct.test-ok = {
    expr = point.verify {
      x = 1;
      y = 2;
    };
    expected = null;
  };
  flake.tests.types-struct.test-not-attrs = {
    expr = point.verify 5;
    expected = "expected type 'point' but value 5 is of type 'int'";
  };
  flake.tests.types-struct.test-missing-member = {
    expr = point.verify { x = 1; };
    expected = "in struct 'point': missing member 'y'";
  };
  flake.tests.types-struct.test-member-type-fail = {
    expr = point.verify {
      x = 1;
      y = "a";
    };
    expected = "in struct 'point': in member 'y': expected type 'int' but value \"a\" is of type 'string'";
  };

  # ── unknown-key policy ──
  flake.tests.types-struct.test-unknown-allowed-by-default = {
    expr = point.verify {
      x = 1;
      y = 2;
      z = 3;
    };
    expected = null;
  };
  flake.tests.types-struct.test-unknown-rejected-when-closed = {
    expr = (point.override { unknown = false; }).verify {
      x = 1;
      y = 2;
      z = 3;
    };
    expected = "in struct 'point': keys ['z'] are unrecognized, expected keys are ['x', 'y']";
  };

  # ── totality ──
  flake.tests.types-struct.test-partial-allowed-when-not-total = {
    expr = (point.override { total = false; }).verify { x = 1; };
    expected = null;
  };
  flake.tests.types-struct.test-empty-allowed-when-not-total = {
    expr = (point.override { total = false; }).verify { };
    expected = null;
  };

  # ── custom whole-record invariant ──
  flake.tests.types-struct.test-custom-verify-fail = {
    expr = (point.override { verify = v: if v.x + v.y == 2 then "VERBOTEN" else null; }).verify {
      x = 1;
      y = 1;
    };
    expected = "in struct 'point': VERBOTEN";
  };
  flake.tests.types-struct.test-custom-verify-ok = {
    expr = (point.override { verify = v: if v.x + v.y == 2 then "VERBOTEN" else null; }).verify {
      x = 1;
      y = 2;
    };
    expected = null;
  };

  # ── nested struct ──
  flake.tests.types-struct.test-nested-ok =
    let
      line = t.struct "line" { a = point; };
    in
    {
      expr = line.verify {
        a = {
          x = 1;
          y = 2;
        };
      };
      expected = null;
    };
  flake.tests.types-struct.test-nested-fail =
    let
      line = t.struct "line" { a = point; };
    in
    {
      expr = line.verify {
        a = {
          x = 1;
          y = "z";
        };
      };
      expected = "in struct 'line': in member 'a': in struct 'point': in member 'y': expected type 'int' but value \"z\" is of type 'string'";
    };

  # ── optionalAttr member ──
  flake.tests.types-struct.test-optional-member-absent-ok =
    let
      cfg = t.struct "cfg" {
        name = t.str;
        port = t.optionalAttr t.int;
      };
    in
    {
      expr = cfg.verify { name = "svc"; };
      expected = null;
    };
  flake.tests.types-struct.test-optional-member-present-typechecked =
    let
      cfg = t.struct "cfg" {
        name = t.str;
        port = t.optionalAttr t.int;
      };
    in
    {
      expr = cfg.verify {
        name = "svc";
        port = "x";
      };
      expected = "in struct 'cfg': in member 'port': in optionalAttr<int>: expected type 'int' but value \"x\" is of type 'string'";
    };

  # ── override composes ──
  #
  # `override` is a delta over the policy set the receiver was built with: a field
  # named in the delta is replaced, a field left unmentioned is retained, and the
  # result carries `override` again, bound to the new set.
  #
  # The four cells below are ABSOLUTE — each pins a literal message rather than
  # comparing two override paths. Their values are chosen against the order of
  # `funcs` in the struct verifier, because `firstFailing` reports one failure and
  # masks the rest: the unknown-key check is observable only once every member
  # check passes, and a custom `verify` only once the members and the unknown check
  # both pass. Each value therefore surfaces the one field its cell is about.
  flake.tests.types-struct.test-chain-total-survives = {
    expr = ((point.override { total = false; }).override { unknown = false; }).verify { x = 1; };
    expected = null;
  };
  flake.tests.types-struct.test-chain-unknown-survives = {
    expr = ((point.override { unknown = false; }).override { total = false; }).verify {
      x = 1;
      y = 2;
      z = 9;
    };
    expected = "in struct 'point': keys ['z'] are unrecognized, expected keys are ['x', 'y']";
  };
  flake.tests.types-struct.test-chain-verify-survives = {
    expr = ((point.override { verify = inv; }).override { unknown = false; }).verify {
      x = 1;
      y = 5;
    };
    expected = "in struct 'point': sum must be 3";
  };
  flake.tests.types-struct.test-chain-three-hops =
    let
      chained = ((point.override { total = false; }).override { verify = inv; }).override {
        unknown = false;
      };
    in
    {
      expr = chained.verify {
        x = 1;
        y = 5;
      };
      expected = "in struct 'point': sum must be 3";
    };

  # Non-commuting deltas on the SAME field: the later one must win. This also holds
  # when each override restarts from the constructor defaults, so it witnesses no
  # composition on its own — it pins the merge direction composition relies on.
  flake.tests.types-struct.test-chain-last-wins = {
    expr = ((point.override { total = false; }).override { total = true; }).verify { x = 1; };
    expected = "in struct 'point': missing member 'y'";
  };

  # SUPPLEMENT, NOT A GATE. A relational cell compares two paths through the same
  # handle, so an `override` broken identically on both sides satisfies it
  # vacuously — an implementation that discards the delta outright passes every
  # instance here. The absolute cells above are what gate the contract; this one
  # states the invariant a future rewrite of the constructor must keep.
  flake.tests.types-struct.test-chain-equals-merged = {
    expr = [
      (law2 { total = false; } { unknown = false; } { x = 1; })
      (law2 { unknown = false; } { total = false; } {
        x = 1;
        y = 2;
        z = 9;
      })
      (law2 { verify = inv; } { unknown = false; } {
        x = 1;
        y = 5;
      })
      (law3 { total = false; } { verify = inv; } { unknown = false; } {
        x = 1;
        y = 5;
      })
    ];
    expected = [
      true
      true
      true
      true
    ];
  };
}
