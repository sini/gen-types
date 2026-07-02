# gen-types: check — throws on error, returns the second argument on success.
{ genTypes, ... }:
let
  t = genTypes;
in
{
  flake.tests.types-check.test-check-returns-second-on-success = {
    expr = t.int.check 5 "the-value";
    expected = "the-value";
  };
  flake.tests.types-check.test-check-identity-usage = {
    # idiomatic: t.check v v — validate-and-pass-through
    expr = t.str.check "hi" "hi";
    expected = "hi";
  };
  flake.tests.types-check.test-check-throws-on-failure = {
    expr = (builtins.tryEval (t.int.check "x" "x")).success;
    expected = false;
  };
  flake.tests.types-check.test-check-struct-passthrough = {
    expr =
      let
        point = t.struct "point" {
          x = t.int;
          y = t.int;
        };
        v = {
          x = 1;
          y = 2;
        };
      in
      point.check v v;
    expected = {
      x = 1;
      y = 2;
    };
  };
}
