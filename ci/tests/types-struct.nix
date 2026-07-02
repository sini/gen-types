# gen-types: struct — totality, unknown-key policy, custom invariants, nesting,
# optionalAttr members, and error-context threading.
{ genTypes, ... }:
let
  t = genTypes;

  point = t.struct "point" {
    x = t.int;
    y = t.int;
  };
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
}
