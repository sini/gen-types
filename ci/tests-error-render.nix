# A name that is not a string refuses BY NAME, catchably, where it is read (see `memberName` and
# `callerName` in lib/checkers.nix). Error-plane cells, beside ./tests-error.nix.
{ genTypes, ... }:
let
  t = genTypes;
in
{
  flake.testsError.types-render.test-union-member-name-not-string-verify = {
    expr =
      (t.union [
        { name = 5; }
        t.string
      ]).verify
        "x";
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: union: member '<unnamed>' is not a checker";
    };
  };
  flake.testsError.types-render.test-union-member-name-not-string-name = {
    expr =
      (t.union [
        { name = 5; }
        t.string
      ]).name;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: union: a member's `name` must be a string";
    };
  };
  flake.testsError.types-render.test-enum-name-not-string = {
    expr = (t.enum 5 [ "a" ]).verify "b";
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: enum: the type's name must be a string";
    };
  };
}
