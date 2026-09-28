# gen-types: validator base — folded from validate.nix, re-expressed purely.
{ genTypes, ... }:
let
  t = genTypes;

  positive = t.mkValidator {
    name = "positive";
    pred = i: i.n > 0;
    message = "n must be positive";
  };
  instancesOk = {
    a = {
      n = 1;
    };
    b = {
      n = 2;
    };
  };
  instancesBad = {
    a = {
      n = 1;
    };
    b = {
      n = -1;
    };
  };
in
{
  flake.tests.types-validate.test-mkValidator-fields = {
    # functions are incomparable in Nix, so assert the plain fields + pred behaviour
    expr =
      let
        v = t.mkValidator {
          name = "positive";
          pred = i: i.n > 0;
          message = "msg";
        };
      in
      {
        inherit (v) name message;
        predOnGood = v.pred { n = 1; };
        predOnBad = v.pred { n = -1; };
      };
    expected = {
      name = "positive";
      message = "msg";
      predOnGood = true;
      predOnBad = false;
    };
  };
  flake.tests.types-validate.test-runValidators-right = {
    expr = t.runValidators "widget" [ positive ] instancesOk;
    expected = {
      right = instancesOk;
    };
  };
  flake.tests.types-validate.test-runValidators-left = {
    expr = t.runValidators "widget" [ positive ] instancesBad;
    expected = {
      left = [
        {
          kind = "widget";
          name = "b";
          validator = "positive";
          message = "n must be positive";
        }
      ];
    };
  };
  flake.tests.types-validate.test-formatErrors = {
    expr = t.formatErrors [
      {
        kind = "widget";
        name = "b";
        validator = "positive";
        message = "n must be positive";
      }
    ];
    expected = "  widget 'b': positive — n must be positive";
  };
  flake.tests.types-validate.test-defaultOnError-throws = {
    expr =
      (builtins.tryEval (
        t.defaultOnError [
          {
            kind = "widget";
            name = "b";
            validator = "positive";
            message = "n must be positive";
          }
        ]
      )).success;
    expected = false;
  };

  # P2 (R7 (a)): the three operands are one required-argument record, a door (`prelude.door`).
  # A missing field is refused at the application's own WHNF, catchably; an extra field is admitted
  # (the record is open); the published map is the native formals the door stands for.
  flake.tests.types-validate.test-mkValidator-door-refuses-a-missing-field-at-application = {
    expr =
      (builtins.tryEval (
        builtins.seq (t.mkValidator {
          name = "n";
          pred = _: true;
        }) null
      )).success;
    expected = false;
  };
  flake.tests.types-validate.test-mkValidator-door-admits-an-extra-field = {
    expr =
      (t.mkValidator {
        name = "n";
        pred = _: true;
        message = "m";
        extra = 1;
      }).message;
    expected = "m";
  };
  flake.tests.types-validate.test-mkValidator-door-publishes-its-formals = {
    expr = [
      (
        t.mkValidator.__functionArgs == builtins.functionArgs (
          {
            name,
            pred,
            message,
            ...
          }:
          null
        )
      )
      t.mkValidator.__contract
    ];
    expected = [
      true
      {
        name = "gen-types.mkValidator";
        required = [
          "name"
          "pred"
          "message"
        ];
        optional = [ ];
        open = true;
      }
    ];
  };
}
