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

  # demanding a self-referential type's identity names the bound, not an evaluator blackhole
  flake.testsError.types-recursive-identity.test-cyclic-identity-refusal-names-the-bound = {
    expr =
      let
        r = t.union [
          t.int
          (t.listOf r)
        ];
      in
      t.idOf r;
    expectedError = {
      type = "ThrownError";
      msg = "^identity: type '.*' has no identity to demand: a type nests deeper than the type-identity depth bound \\(128 levels\\); a self-referential type has no identity$";
    };
  };

  # `idOf` refuses by name a value carrying no `__mint`: a foreign record, and a non-record
  flake.testsError.types-identity.test-idOf-refuses-a-record-with-no-mint = {
    expr = t.idOf { name = "foreign"; };
    expectedError = {
      type = "ThrownError";
      msg = "^identity: type 'foreign' carries no `__mint`: it is no type record of this vocabulary, so it has no identity to demand$";
    };
  };
  flake.testsError.types-identity.test-idOf-refuses-a-non-record = {
    expr = t.idOf 3;
    expectedError = {
      type = "ThrownError";
      msg = "^identity: a int carries no `__mint`: it is no type record of this vocabulary, so it has no identity to demand$";
    };
  };

  # `__sealed` is TOTAL on every producer of a minted type, so `idOf` reads it directly and refuses a
  # minted record without one by name rather than reading it as `{ }` (den-hoag-6orb8 A1)
  flake.testsError.types-identity.test-idOf-refuses-a-mint-without-sealed = {
    expr = t.idOf {
      name = "half";
      __mint.minted = "type:dddd";
    };
    expectedError = {
      type = "ThrownError";
      msg = "^identity: type 'half' carries a mint and no `__sealed`: its producer states no sealed components, so its mark cannot be read as an identity$";
    };
  };

  # `payloadOf` names the record and why it cannot certify: a stale payload carried by `//`
  flake.testsError.types-payload.test-payloadOf-refusal-names-a-stale-payload = {
    expr = t.payloadOf (t.int // { inherit (t.enum "e" [ "a" ]) __payload; });
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: payloadOf: `int' has no readable construction payload: its `__payload' is not the preimage of its own digest";
    };
  };

  # and one with a sealed component (a minted mark beside a caller lambda)
  flake.testsError.types-payload.test-payloadOf-refusal-names-a-sealed-identity = {
    expr = t.payloadOf (t.typedef' "t" (_: null));
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: payloadOf: `t' has no readable construction payload: it carries sealed component\\(s\\), so its payload is not a total preimage";
    };
  };

  # the predicate door names itself, the type and the accepted forms, catchably, where a record or an
  # integer used to abort uncatchably at the first `verify` (den-hoag-6orb8 U1-wf)
  flake.testsError.types-identity-sealed.test-predicate-door-names-the-accepted-forms = {
    expr = t.typedef "tally" 3;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: typedef: the predicate of type 'tally' must be a function or a registered construction \\(gen-algebra `mkIntensional`\\), but it is of type 'int'";
    };
  };
  flake.testsError.types-identity-sealed.test-predicate-door-refuses-a-record = {
    expr = (t.typedef "tally" { lo = 1; }).verify 1;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: typedef: the predicate of type 'tally' must be a function or a registered construction \\(gen-algebra `mkIntensional`\\), but it is of type 'set'";
    };
  };

  # demanding the identity of a composite over a member whose `check` a wrapper rewrote names the
  # sealed member (den-hoag-ydro3: a rewritten member is a sealed component)
  flake.testsError.types-added-check.test-idOf-refusal-names-a-rewritten-check = {
    expr =
      let
        own = t.int // t.witnessedCheck (x: t.int.verify x == null);
      in
      t.idOf (t.listOf (own // { check = x: own.check x && x < 3; }));
    expectedError = {
      type = "ThrownError";
      msg = "identity: type 'listOf<int>' has sealed component\\(s\\) 'members.0' \\(a caller-supplied lambda, a registered construction, or a type with no minted identity\\), which its mark is blind to: it is decided by `typeEq` and has no identity to demand";
    };
  };

  # `mkValidator`'s record door names the missing field and the door (P2, R7 (a))
  flake.testsError.types-validate.test-mkValidator-missing-field-named = {
    expr = t.mkValidator {
      name = "n";
      pred = _: true;
    };
    expectedError = {
      type = "ThrownError";
      msg = "gen-types.mkValidator: required field 'message' is missing";
    };
  };

  # a functor whose `__functor` throws propagates its own error through `function`, so a union
  # with a `function` member throws rather than serving the `attrs` member, as nixpkgs'
  # `either (functionTo raw) attrs` does (den-hoag-b5qdr)
  flake.testsError.types-function.test-throwing-functor-propagates-through-union = {
    expr =
      (t.union [
        t.function
        t.attrs
      ]).verify
        { __functor = _: throw "b5qdr: the functor's own error"; };
    expectedError = {
      type = "ThrownError";
      msg = "b5qdr: the functor's own error";
    };
  };

  # a set whose `__toString` throws propagates its own error through `path`, which coerces it to
  # test absoluteness, so a union with a `path` member throws rather than serving the `attrs`
  # member, as nixpkgs' `either path attrs` does (den-hoag-fyx6m)
  flake.testsError.types-path.test-throwing-toString-propagates-through-union = {
    expr =
      (t.union [
        t.path
        t.attrs
      ]).verify
        { __toString = _: throw "fyx6m: the coercion's own error"; };
    expectedError = {
      type = "ThrownError";
      msg = "fyx6m: the coercion's own error";
    };
  };
}
