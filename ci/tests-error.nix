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
{
  genTypes,
  prelude,
  algebra,
  lib,
  ...
}:
let
  # gen-prelude's refusal text, composed with this library's own literal door, field and required set
  # (den-hoag-7jltk): every assertion kept, none of gen-prelude's wording copied.
  inherit (prelude) refusals;
  t = genTypes;
  # a merge strategy's shape: a name and a domain, no `verify` (as in ./tests/types-poly.nix)
  strategy = {
    name = "strategy";
    admits = _: true;
  };

  # ── the evaluator divergences (README "Evaluator divergences (stated)") ──
  # `==` compares a function by its value SLOT on upstream Nix and Determinate and by its OBJECT on
  # Lix, so one function reached through two slots splits them. These cells run here, on the plane
  # each evaluator runs itself. A verdict reads `"REFUSED"` for a caught refusal.
  verdict =
    v:
    let
      o = builtins.tryEval (builtins.deepSeq v v);
    in
    if o.success then o.value else "REFUSED";
  teq = a: b: verdict (t.typeEq a b);
  # the RUNNING evaluator's own `==` on a literal shape that holds one function in two slots, so a
  # stated split is held to that evaluator's fact and to no binding of this library
  ownEq =
    x: y:
    let
      o = builtins.tryEval (x == y);
    in
    o.success && o.value;
  twoSlots = ownEq { c = sl.f; } { c = sl.f; };
  asRefusal = b: if b then true else "REFUSED";
  sl = {
    f = x: x;
    # the unapplied `enum` (`name0: elems:`), the member of the shape that found the split
    enumFn = t.enum [
      "a"
      "b"
    ];
    pos = x: x > 0;
    even = x: builtins.bitAnd x 1 == 0;
    verify = x: if x > 0 then null else "negative";
  };
  pos = sl.pos;
  even = sl.even;
  verifyPos = sl.verify;
  rebuild = builtins.mapAttrs (_: v: v);
  foreignList = lib.types.listOf lib.types.int;
  foreignEnum = lib.types.enum [
    "a"
    "b"
  ];
  refinedCheck =
    f:
    t.refined t.int [
      {
        check = f;
        message = "positive";
      }
    ];
  structVerify = f: (t.struct "s" { a = t.int; }).override { verify = f; };
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
          (t.checkedListOf r)
        ];
      in
      t.idOf r;
    expectedError = {
      type = "ThrownError";
      msg = "^gen-types: idOf: type '.*' has no identity to demand: a type nests deeper than the type-identity depth bound \\(128 levels\\); a self-referential type has no identity$";
    };
  };

  # a `//` copy carries its base's mark and so its base's digest: `idOf` refuses it by name, as `typeEq`,
  # `identityOf` and `payloadOf` do, never answering the base's identity for a type that is not it
  flake.testsError.types-identity.test-idOf-refuses-a-copy-of-a-type = {
    expr = t.idOf (t.int // { verify = _: null; });
    expectedError = {
      type = "ThrownError";
      msg = "^gen-types: idOf: `int' is a `//' copy or a wrapper that rewrote its check: its mark names its base, so it has no identity to demand$";
    };
  };

  # `idOf` refuses by name a value carrying no `__mint`: a foreign record, and a non-record
  flake.testsError.types-identity.test-idOf-refuses-a-record-with-no-mint = {
    expr = t.idOf { name = "foreign"; };
    expectedError = {
      type = "ThrownError";
      msg = "^gen-types: idOf: `foreign' carries no `__mint`: it is no type record of this vocabulary, so it has no identity to demand$";
    };
  };
  flake.testsError.types-identity.test-idOf-refuses-a-non-record = {
    expr = t.idOf 3;
    expectedError = {
      type = "ThrownError";
      msg = "^gen-types: idOf: a int carries no `__mint`: it is no type record of this vocabulary, so it has no identity to demand$";
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
      msg = "^gen-types: idOf: `half' carries a mint and no `__sealed`: its producer states no sealed components, so its mark cannot be read as an identity$";
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
    expr = t.typedef { } "tally" 3;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: typedef: the predicate of type 'tally' must be a function or a registered construction \\(gen-algebra `mkIntensional`\\), but it is of type 'int'";
    };
  };
  flake.testsError.types-identity-sealed.test-predicate-door-refuses-a-record = {
    expr = (t.typedef { } "tally" { lo = 1; }).verify 1;
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
      t.idOf (t.checkedListOf (own // { check = x: own.check x && x < 3; }));
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: idOf: type 'listOf<int>' has sealed component\\(s\\) 'members.0' \\(a caller-supplied lambda, a registered construction, or a type with no minted identity\\), which its mark is blind to: it is decided by `typeEq` and has no identity to demand";
    };
  };

  # `typedef`'s options come first and are closed (den-hoag-6orb8 U3-m3, U3-m5, totality): the
  # positional form names the options-first one, an unknown option names the door and `merge`, and a
  # `merge` that is no function is refused where the type is built
  flake.testsError.types-typedef-merge.test-the-positional-form-names-the-options-first-form = {
    expr = t.typedef "tally" builtins.isInt;
    expectedError = {
      type = "ThrownError";
      msg = "^gen-types: typedef: the positional form `typedef \"tally\" <predicate>` is retired; the options come first: `typedef \\{ \\} \"tally\" <predicate>`, or `typedef \\{ merge = loc: defs: <value>; \\} \"tally\" <predicate>`$";
    };
  };
  flake.testsError.types-typedef-merge.test-an-unknown-option-names-typedef-and-merge = {
    expr = t.typedef { mrege = _: _: 0; } "tally" builtins.isInt;
    expectedError = {
      type = "ThrownError";
      msg =
        "^" + prelude.escapeRegex (refusals.unknownOption "gen-types: typedef" [ "merge" ] "mrege") + "$";
    };
  };
  flake.testsError.types-typedef-merge.test-a-merge-that-is-no-function-is-refused = {
    expr = t.typedef { merge = 3; } "tally" builtins.isInt;
    expectedError = {
      type = "ThrownError";
      msg = "gen-types: typedef: the merge of type 'tally' must be a function or a registered construction \\(gen-algebra `mkIntensional`\\), but it is of type 'int'";
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
      msg =
        "^"
        + prelude.escapeRegex (
          refusals.missingField "gen-types.mkValidator" [ "name" "pred" "message" ] "message"
        )
        + "$";
    };
  };

  # a functor whose `__functor` throws propagates its own error through `function`, so a union
  # with a `function` member throws rather than serving the `attrs` member, as nixpkgs'
  # `either (functionTo raw) attrs` does (den-hoag-b5qdr)
  flake.testsError.types-function.test-throwing-functor-propagates-through-union = {
    expr =
      (t.union [
        t.function
        t.checkedAttrs
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
        t.checkedAttrs
      ]).verify
        { __toString = _: throw "fyx6m: the coercion's own error"; };
    expectedError = {
      type = "ThrownError";
      msg = "fyx6m: the coercion's own error";
    };
  };

  # A refinement is a `{ check, message }` record; any other shape is refused BY NAME where `refined`
  # takes it, catchably, where it used to abort uncatchably when a value was first checked
  # (den-hoag-c9cr1, the gen-schema den-hoag-ub19x class). Each refusal names the position and the fault.
  flake.testsError.types-refined =
    let
      refuses = fault: {
        type = "ThrownError";
        msg = "^gen-types: refined: refinement ${fault}\\. A refinement is a record `\\{ check = <value -> bool>; message = \"<what a violation reports>\"; \\}`; ";
      };
      rt = r: t.refined t.int r;
      withCheck = check: {
        inherit check;
        message = "positive";
      };
      chain = n: leaf: if n == 0 then leaf else { __functor = _: chain (n - 1) leaf; };
      bound = "a functor that reaches no function within 32 `__functor` steps";
      # what Nix applies as `leaf`: nested, a functor-valued `__functor`, 32 steps, stacked
      # `setFunctionArgs` (nixpkgs' encoding, written out)
      applicable = leaf: [
        { __functor = _: { __functor = _: leaf; }; }
        {
          __functor = {
            __functor = _: _: leaf;
          };
        }
        (chain 32 leaf)
        {
          __functor = _: {
            __functor = _: leaf;
            __functionArgs = { };
          };
          __functionArgs = { };
        }
      ];
      ok = {
        check = pos;
        message = "positive";
      };
    in
    {
      test-a-bare-function-refinement-is-refused = {
        expr = rt pos;
        expectedError = refuses "0 is of type `lambda`, not a refinement record";
      };
      test-a-string-refinement-is-refused = {
        expr = rt "x";
        expectedError = refuses "0 is of type `string`, not a refinement record";
      };
      test-an-int-refinement-is-refused = {
        expr = rt 3;
        expectedError = refuses "0 is of type `int`, not a refinement record";
      };
      test-a-refinement-without-check-is-refused = {
        expr = rt { message = "m"; };
        expectedError = refuses "0 has no `check`";
      };
      test-a-refinement-without-message-is-refused = {
        expr = rt { check = pos; };
        expectedError = refuses "0 has no `message`";
      };
      test-a-refinement-with-a-non-function-check-is-refused = {
        expr = rt {
          check = 3;
          message = "m";
        };
        expectedError = refuses "0 has a `check` of type `int`, not a function";
      };
      test-a-refinement-with-a-non-string-message-is-refused = {
        expr = rt {
          check = pos;
          message = 3;
        };
        expectedError = refuses "0 has a `message` of type `int`, not a string";
      };
      test-the-position-of-a-bad-refinement-in-a-list-is-named = {
        expr = rt [
          ok
          pos
        ];
        expectedError = refuses "1 is of type `lambda`, not a refinement record";
      };
      # controls, same plane: a record, a list of records and a functor check are taken
      test-control-a-record-refinement-is-taken = {
        expr = (rt ok).verify (-1);
        expected = "positive";
      };
      test-control-a-list-of-records-is-taken = {
        expr =
          (rt [
            ok
            t.refinements.tcpPort
          ]).verify
            70000;
        expected = "must be a valid TCP port (1-65535)";
      };
      # den-hoag-b6nyh: `check` is admitted by what Nix can apply (gen-prelude `isApplicable`); a
      # functor Nix cannot apply is refused where `refined` takes it, where `verify` and the
      # two-argument `check` aborted on it before. What Nix applies is served as its lambda.
      test-a-functor-check-returning-a-non-function-is-refused = {
        expr =
          (rt (withCheck {
            __functor = _: 5;
          })).verify
            1;
        expectedError = refuses "0 has a `check` of type `set`, not a function";
      };
      test-a-functor-check-returning-a-non-function-is-catchable = {
        expr =
          (builtins.tryEval (
            (rt (withCheck {
              __functor = _: 5;
            })).check
              1
              1
          )).success;
        expected = false;
      };
      test-a-self-returning-functor-check-is-refused-naming-the-bound = {
        expr =
          (rt (
            withCheck (
              let
                s = {
                  __functor = self: self;
                };
              in
              s
            )
          )).check
            1
            1;
        expectedError = refuses "0 has a `check` of type `set` \\(${bound}\\), not a function";
      };
      test-a-33-level-functor-check-is-refused-naming-the-bound = {
        expr = (rt (withCheck (chain 33 pos))).verify 1;
        expectedError = refuses "0 has a `check` of type `set` \\(${bound}\\), not a function";
      };
      test-applicable-functor-checks-are-served-as-their-lambda = {
        expr = map (c: [
          ((rt (withCheck c)).verify 1)
          ((rt (withCheck c)).verify (-1))
          ((rt (withCheck c)).check 1 1)
        ]) (applicable pos);
        expected = builtins.genList (_: [
          null
          "positive"
          1
        ]) 4;
      };
      test-control-a-functor-check-is-taken = {
        expr =
          (rt {
            check = {
              __functor = _: pos;
            };
            message = "positive";
          }).verify
            (-1);
        expected = "positive";
      };
    };

  # ★ CLOSED BY CONSTRUCTION (`mkIdentity`'s member arm): a member that is a function has no identity,
  # so two constructions over it are refused on all three evaluators, where Lix used to answer `true`
  # through two slots of one function. One construction against itself stays `true` ×3. RED on Lix
  # with the arm's closure reverted. (`refined`'s bare-function refinement arm is gone: a refinement
  # that is not a `{ check, message }` record is refused where it enters, `types-refined` below.)
  flake.testsError.types-evaluator-divergences = {
    test-a-function-member-in-two-constructions-is-refused-on-every-evaluator = {
      expr = teq (t.checkedListOf sl.enumFn) (t.checkedListOf sl.enumFn);
      expected = "REFUSED";
    };
    test-a-function-member-in-one-construction-is-itself = {
      expr =
        let
          x = t.checkedListOf sl.enumFn;
        in
        teq x x;
      expected = true;
    };
    # gen-algebra `conservativeEq`'s own entry to `sealedCollisionEq`, over the same subjects
    test-algebra-conservativeEq-refuses-a-function-member-in-two-constructions = {
      expr = verdict (algebra.conservativeEq (t.checkedListOf sl.enumFn) (t.checkedListOf sl.enumFn));
      expected = "REFUSED";
    };
    test-algebra-conservativeEq-holds-of-a-function-member-in-one-construction = {
      expr =
        let
          x = t.checkedListOf sl.enumFn;
        in
        verdict (algebra.conservativeEq x x);
      expected = true;
    };

    # ★ STATED DIVERGENCES. Each split cell holds the site's verdict to the running evaluator's own
    # `==` over a literal two-slot shape (false on Nix and Determinate, `true` on Lix), so it reds on
    # any evaluator whose site stops answering as its `==` does. Each partner is the verdict a closure
    # at the site would move, `true` ×3.
    # s3: the compared arm, `comparisonSubject a == comparisonSubject b`, over a foreign record
    # rebuilt by a `mapAttrs` copy (each closure field a fresh slot)
    test-a-rebuilt-foreign-listOf-answers-as-the-evaluator-s-own-identity = {
      expr = teq foreignList (rebuild foreignList) == twoSlots;
      expected = true;
    };
    test-a-rebuilt-foreign-enum-answers-as-the-evaluator-s-own-identity = {
      expr = teq foreignEnum (rebuild foreignEnum) == twoSlots;
      expected = true;
    };
    test-a-foreign-type-is-itself = {
      expr = {
        listOf = teq foreignList foreignList;
        str = teq lib.types.str lib.types.str;
      };
      expected = {
        listOf = true;
        str = true;
      };
    };
    # s4: `stampAgrees` through `stampOk`, over a `//` that restates a closure field by selection
    test-a-restated-verify-answers-as-the-evaluator-s-own-identity = {
      expr = teq t.int (t.int // { verify = t.int.verify; }) == asRefusal twoSlots;
      expected = true;
    };
    test-a-restated-check-answers-as-the-evaluator-s-own-identity = {
      expr = teq t.int (t.int // { check = t.int.check; }) == asRefusal twoSlots;
      expected = true;
    };
    test-int-is-itself-and-a-slice-restated-is-int = {
      expr = {
        intInt = teq t.int t.int;
        sliceRestated = teq t.int (t.int // builtins.intersectAttrs { verify = null; } t.int);
      };
      expected = {
        intInt = true;
        sliceRestated = true;
      };
    };
    # `sealedArg`: a constructor's own caller predicate, sealed in the slot it was passed in, through
    # each caller (`typedef`, `typedef'`, `struct`'s `verify`)
    test-a-typedef-predicate-by-selection-answers-as-the-evaluator-s-own-identity = {
      expr = teq (t.typedef { } "even" sl.even) (t.typedef { } "even" sl.even) == asRefusal twoSlots;
      expected = true;
    };
    test-a-typedef-prime-verifier-by-selection-answers-as-the-evaluator-s-own-identity = {
      expr = teq (t.typedef' "v" sl.verify) (t.typedef' "v" sl.verify) == asRefusal twoSlots;
      expected = true;
    };
    test-a-struct-verify-by-selection-answers-as-the-evaluator-s-own-identity = {
      expr = teq (structVerify sl.verify) (structVerify sl.verify) == asRefusal twoSlots;
      expected = true;
    };
    test-a-bound-caller-predicate-is-one-type = {
      expr = {
        typedef = teq (t.typedef { } "even" even) (t.typedef { } "even" even);
        typedefPrime = teq (t.typedef' "v" verifyPos) (t.typedef' "v" verifyPos);
        structVerify = teq (structVerify verifyPos) (structVerify verifyPos);
      };
      expected = {
        typedef = true;
        typedefPrime = true;
        structVerify = true;
      };
    };
    # `refined`'s check slice: a refinement record's `check`, sealed in its slot
    test-a-refinement-check-by-selection-answers-as-the-evaluator-s-own-identity = {
      expr = teq (refinedCheck sl.pos) (refinedCheck sl.pos) == asRefusal twoSlots;
      expected = true;
    };
    test-a-bound-refinement-check-is-one-type = {
      expr = teq (refinedCheck pos) (refinedCheck pos);
      expected = true;
    };
  };
}
