# gen-types: primitive checkers — success (null) and failure (error string).
{ genTypes, ... }:
let
  t = genTypes;
in
{
  flake.tests.types-prim.test-string-ok = {
    expr = t.string.verify "hello";
    expected = null;
  };
  flake.tests.types-prim.test-str-alias-ok = {
    expr = t.str.verify "hello";
    expected = null;
  };
  flake.tests.types-prim.test-string-fail = {
    expr = t.string.verify 1;
    expected = "expected type 'string' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-int-ok = {
    expr = t.int.verify 5;
    expected = null;
  };
  flake.tests.types-prim.test-int-fail = {
    expr = t.int.verify true;
    expected = "expected type 'int' but value true is of type 'bool'";
  };
  flake.tests.types-prim.test-bool-ok = {
    expr = t.bool.verify false;
    expected = null;
  };
  flake.tests.types-prim.test-bool-fail = {
    expr = t.bool.verify 1;
    expected = "expected type 'bool' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-float-ok = {
    expr = t.float.verify 1.5;
    expected = null;
  };
  flake.tests.types-prim.test-float-fail-on-int = {
    expr = t.float.verify 1;
    expected = "expected type 'float' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-number-accepts-int = {
    expr = t.number.verify 1;
    expected = null;
  };
  flake.tests.types-prim.test-number-accepts-float = {
    expr = t.number.verify 1.5;
    expected = null;
  };
  flake.tests.types-prim.test-number-fail = {
    expr = t.number.verify "x";
    expected = "expected type 'number' but value \"x\" is of type 'string'";
  };
  flake.tests.types-prim.test-path-ok = {
    expr = t.path.verify ./.;
    expected = null;
  };
  flake.tests.types-prim.test-path-fail = {
    expr = t.path.verify "not a path";
    expected = "expected type 'path' but value \"not a path\" is of type 'string'";
  };
  flake.tests.types-prim.test-pathLike-accepts-string = {
    expr = t.pathLike.verify "some/string";
    expected = null;
  };
  flake.tests.types-prim.test-pathLike-accepts-path = {
    expr = t.pathLike.verify ./.;
    expected = null;
  };
  flake.tests.types-prim.test-pathLike-fail = {
    expr = t.pathLike.verify 1;
    expected = "expected type 'pathLike' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-attrs-ok = {
    expr = t.attrs.verify { a = 1; };
    expected = null;
  };
  flake.tests.types-prim.test-attrs-fail = {
    expr = t.attrs.verify [ 1 ];
    expected = "expected type 'attrs' but value [ 1 ] is of type 'list'";
  };
  flake.tests.types-prim.test-list-ok = {
    expr = t.list.verify [
      1
      2
    ];
    expected = null;
  };
  flake.tests.types-prim.test-list-fail = {
    expr = t.list.verify { };
    expected = "expected type 'list' but value {  } is of type 'set'";
  };
  flake.tests.types-prim.test-function-ok = {
    expr = t.function.verify (x: x);
    expected = null;
  };
  flake.tests.types-prim.test-function-fail = {
    expr = t.function.verify 1;
    expected = "expected type 'function' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-derivation-fail-on-attrs = {
    expr = t.derivation.verify { type = "not-drv"; };
    expected = "expected type 'derivation' but value { type = \"not-drv\"; } is of type 'set'";
  };
  flake.tests.types-prim.test-derivation-ok-on-fake-drv = {
    expr = t.derivation.verify {
      type = "derivation";
      name = "x";
    };
    expected = null;
  };
  flake.tests.types-prim.test-null-ok = {
    expr = t.null.verify null;
    expected = null;
  };
  flake.tests.types-prim.test-null-fail = {
    expr = t.null.verify 1;
    expected = "expected type 'null' but value 1 is of type 'int'";
  };
  flake.tests.types-prim.test-any-accepts-anything = {
    expr = [
      (t.any.verify 1)
      (t.any.verify "x")
      (t.any.verify null)
      (t.any.verify [ ])
    ];
    expected = [
      null
      null
      null
      null
    ];
  };
  flake.tests.types-prim.test-never-rejects-everything = {
    expr = t.never.verify 1;
    expected = "expected type 'never' but value 1 is of type 'int'";
  };
}
