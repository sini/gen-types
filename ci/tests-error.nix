# THE SECOND TEST OUTPUT: cells whose subject is an ERROR's message.
#
# `builtins.tryEval` can assert THAT a checker refuses, and the suites under ./tests do. WHICH
# refusal it was is a claim about the message, and `tryEval` discards the message; the only
# assertion for it is nix-unit's `expectedError`.
#
# ★ WHY A SECOND OUTPUT. `gen-harness.lib.mkCi` builds `checks.default` from an asserter that
# evaluates every `flake.tests` `expr` UNCONDITIONALLY, so a throwing `expr` there crashes the
# gate rather than failing a cell. These cells live on `flake.testsError`, outside that
# quantifier, and reach the flake through `mkCi`'s `extraModules` rather than `testModules`, so
# the split depends on no filter predicate.
#
#   nix-unit --flake ./ci#tests        # the suites
#   nix-unit --flake ./ci#testsError   # these cells
{ genTypes, ... }:
let
  t = genTypes;
  # a merge strategy's shape: a name and a domain, no `verify` (as in ./tests/types-poly.nix)
  strategy = {
    name = "strategy";
    admits = _: true;
  };
in
{
  # the refusal names the combinator and the member
  flake.testsError.types-poly.test-cyiuz-refusal-names-combinator-and-member = {
    expr =
      (t.union [
        strategy
        t.str
      ]).verify
        1;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: union: member 'strategy' is not a checker";
    };
  };
}
