# gen-types: strict — closed-world unknown-key rejection (folded from strict.nix).
{ genTypes, ... }:
let
  t = genTypes;
  s = t.strict [
    "a"
    "b"
  ];
in
{
  flake.tests.types-strict.test-known-keys-ok = {
    expr = s.verify {
      a = 1;
      b = 2;
    };
    expected = null;
  };
  flake.tests.types-strict.test-subset-ok = {
    expr = s.verify { a = 1; };
    expected = null;
  };
  flake.tests.types-strict.test-unknown-key-fail = {
    expr = s.verify {
      a = 1;
      c = 3;
    };
    expected = "keys ['c'] are unrecognized, expected keys are ['a', 'b']";
  };
  flake.tests.types-strict.test-not-attrs-fail = {
    expr = s.verify 5;
    expected = "expected an attribute set for strict-key checking, got int";
  };
}
