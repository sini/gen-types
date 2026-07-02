# gen-types: intensional identity — __name, __id, typeEq (Palmer-style name-only).
{ genTypes, ... }:
let
  t = genTypes;
in
{
  flake.tests.types-identity.test-basename-primitive = {
    expr = t.int.__name;
    expected = "int";
  };
  flake.tests.types-identity.test-basename-strips-poly = {
    expr = (t.listOf t.int).__name;
    expected = "listOf";
  };
  flake.tests.types-identity.test-fullname-keeps-poly = {
    expr = (t.listOf t.int).name;
    expected = "listOf<int>";
  };
  flake.tests.types-identity.test-id-is-sha256-hex = {
    expr = builtins.stringLength t.int.__id;
    expected = 64;
  };
  flake.tests.types-identity.test-typeEq-same-structural-name = {
    # two independently-constructed listOf<int> are intensionally equal
    expr = t.typeEq (t.listOf t.int) (t.listOf t.int);
    expected = true;
  };
  flake.tests.types-identity.test-typeEq-different-names = {
    expr = t.typeEq t.int t.str;
    expected = false;
  };
  flake.tests.types-identity.test-typeEq-primitive-self = {
    expr = t.typeEq t.int t.int;
    expected = true;
  };
  flake.tests.types-identity.test-typeEq-nested-distinct = {
    expr = t.typeEq (t.listOf t.int) (t.listOf t.str);
    expected = false;
  };
  flake.tests.types-identity.test-intensionalEq-alias = {
    expr = t.intensionalEq t.bool t.bool;
    expected = true;
  };
  flake.tests.types-identity.test-str-alias-shares-identity = {
    # str is a definitional alias of string; both carry name "string"
    expr = t.typeEq t.str t.string;
    expected = true;
  };
}
