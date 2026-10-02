# gen-types: `function` admits exactly what nixpkgs' `lib.isFunction` admits (den-hoag-b5qdr). A
# functor whose `__functor` returns a function is a function: nixpkgs' `setFunctionArgs` wrapper,
# gen-prelude's own `door` and gen-types' own `witnessedCheck` `.check` are all that shape. A functor whose `__functor` is not a function, or
# returns a non-function, is refused, as an attrset is. RED under `builtins.isFunction`: every
# functor row refuses.
{
  genTypes,
  prelude,
  lib,
  ...
}:
let
  t = genTypes;
  id = x: x;
  battery = {
    lambda = id;
    functor = {
      __functor = _: id;
    };
    setFunctionArgs = lib.setFunctionArgs id { };
    setFunctionArgsFormals = lib.setFunctionArgs ({ a, ... }: a) { a = false; };
    door = prelude.door;
    witnessedCheck = (t.witnessedCheck (_: true)).check;
    nonFunctionFunctor = {
      __functor = 5;
    };
    functorToValue = {
      __functor = _: 5;
    };
    nestedFunctor = {
      __functor = {
        __functor = _: _: id;
      };
    };
    setFunctionArgsOverFunctor = lib.setFunctionArgs (lib.setFunctionArgs id { }) { };
    attrs = {
      a = 1;
    };
    string = "x";
    null = null;
  };
  admits = v: t.function.verify v == null;
in
{
  flake.tests.types-function.test-functor-ok = {
    expr = t.function.verify battery.functor;
    expected = null;
  };
  flake.tests.types-function.test-setFunctionArgs-ok = {
    expr = t.function.verify battery.setFunctionArgs;
    expected = null;
  };
  flake.tests.types-function.test-door-ok = {
    expr = t.function.verify battery.door;
    expected = null;
  };
  flake.tests.types-function.test-witnessedCheck-ok = {
    expr = t.function.verify battery.witnessedCheck;
    expected = null;
  };
  flake.tests.types-function.test-non-function-functor-fail = {
    expr = t.function.verify battery.nonFunctionFunctor;
    expected = "expected type 'function' but value { __functor = …; } is of type 'set'";
  };
  # the differential: no battery value on which gen and nixpkgs disagree
  flake.tests.types-function.test-agrees-with-lib-isFunction = {
    expr = builtins.filter (n: admits battery.${n} != lib.isFunction battery.${n}) (
      builtins.attrNames battery
    );
    expected = [ ];
  };
  # control: the battery straddles the predicate, so the differential cannot pass on a collapsed one
  flake.tests.types-function.test-control-battery-straddles = {
    expr = builtins.filter (n: lib.isFunction battery.${n}) (builtins.attrNames battery);
    expected = [
      "door"
      "functor"
      "lambda"
      "setFunctionArgs"
      "setFunctionArgsFormals"
      "witnessedCheck"
    ];
  };
}
