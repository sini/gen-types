# gen-types: refined — base checker + predicate contracts (folded from refined.nix).
{ genTypes, ... }:
let
  t = genTypes;
in
{
  flake.tests.types-refined.test-positive-ok = {
    expr = (t.refined t.int t.refinements.positive).verify 5;
    expected = null;
  };
  flake.tests.types-refined.test-positive-fail = {
    expr = (t.refined t.int t.refinements.positive).verify (-1);
    expected = "must be positive";
  };
  flake.tests.types-refined.test-base-checked-first = {
    # base type failure short-circuits before predicates run
    expr = (t.refined t.int t.refinements.positive).verify "x";
    expected = "expected type 'int' but value \"x\" is of type 'string'";
  };
  flake.tests.types-refined.test-nonEmpty-fail = {
    expr = (t.refined t.str t.refinements.nonEmpty).verify "";
    expected = "must not be empty";
  };
  flake.tests.types-refined.test-nonEmpty-ok = {
    expr = (t.refined t.str t.refinements.nonEmpty).verify "hi";
    expected = null;
  };
  flake.tests.types-refined.test-tcpPort-ok = {
    expr = (t.refined t.int t.refinements.tcpPort).verify 8080;
    expected = null;
  };
  flake.tests.types-refined.test-tcpPort-fail = {
    expr = (t.refined t.int t.refinements.tcpPort).verify 70000;
    expected = "must be a valid TCP port (1-65535)";
  };
  flake.tests.types-refined.test-list-of-refinements = {
    # multiple predicates in one pass; first failure reported
    expr =
      (t.refined t.int [
        t.refinements.positive
        t.refinements.tcpPort
      ]).verify
        0;
    expected = "must be positive";
  };
  flake.tests.types-refined.test-name = {
    expr = (t.refined t.int t.refinements.positive).name;
    expected = "refined<int>";
  };
  flake.tests.types-refined.test-introspection = {
    expr = builtins.length (t.refined t.int t.refinements.positive).__refinements;
    expected = 1;
  };
}
