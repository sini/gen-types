# gen-types: `function` admits exactly what nixpkgs' `lib.isFunction` admits (den-hoag-b5qdr). A
# functor whose `__functor` reaches a function is a function: nixpkgs' `setFunctionArgs` wrapper,
# gen-prelude's own `door` and gen-types' own `witnessedCheck` `.check` are all that shape, and so
# are a nested functor and a `setFunctionArgs` over one (nixpkgs #574597, den-hoag-b6nyh). A functor
# whose `__functor` is not a function, or returns a non-function, is refused, as an attrset is. RED
# under `builtins.isFunction`: every functor row refuses.
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
  chain = n: if n == 0 then id else { __functor = _: chain (n - 1); };
  self = {
    __functor = s: s;
  };
  fnOrAttrs = t.union [
    t.function
    t.checkedAttrs
  ];
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
  # control: the battery straddles the predicate, so the differential cannot pass on a collapsed one.
  # It pins nixpkgs' own predicate, so nixpkgs' move moves it: #574597 (`85effade`, nixpkgs-lib
  # `7851ba6`) answers the two nested rows true again, as before #520296.
  flake.tests.types-function.test-control-battery-straddles = {
    expr = builtins.filter (n: lib.isFunction battery.${n}) (builtins.attrNames battery);
    expected = [
      "door"
      "functor"
      "lambda"
      "nestedFunctor"
      "setFunctionArgs"
      "setFunctionArgsFormals"
      "setFunctionArgsOverFunctor"
      "witnessedCheck"
    ];
  };
  # `function` is the bool form under a union: a functor whose walk exhausts gen-prelude's bound is
  # refused by `function` alone and served by the `checkedAttrs` member, as at b5qdr
  flake.tests.types-function.test-union-serves-an-exhausted-functor-by-its-other-member = {
    expr = map (v: fnOrAttrs.verify v) [
      self
      (chain 33)
    ];
    expected = [
      null
      null
    ];
  };
  # control, same cells: `function` alone refuses both, and serves the 32-level chain
  flake.tests.types-function.test-control-function-alone-refuses-an-exhausted-functor = {
    expr = map (v: t.function.verify v == null) [
      self
      (chain 33)
      (chain 32)
    ];
    expected = [
      false
      false
      true
    ];
  };
}
