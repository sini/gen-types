# gen-types: validator base — folded from validate.nix, re-expressed purely.
{ genTypes, ... }:
let
  t = genTypes;

  positive = t.mkValidator "positive" (i: i.n > 0) "n must be positive";
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
        v = t.mkValidator "positive" (i: i.n > 0) "msg";
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
}
