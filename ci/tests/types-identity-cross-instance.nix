# gen-types: a COMPARED-regime `typeEq` decides a pair whose records carry a back-edge. The
# synthetic pair's back-edge sits under `description`, which every evaluator interns at startup,
# so `==` reaches it before `check` in every evaluation context: RED is an uncatchable overflow
# independent of parse order. The nixpkgs cross-instance pairs are the consumer shape.
# `derivedDiffers` and `shallowCopy` share every closure slot, so only the whole record decides
# them: a subject of closures alone reads `derivedDiffers = true`.
{ genTypes, lib, ... }:
let
  t = genTypes;
  ft = lib.types;
  u = (lib.extend (_: _: { })).types;
  mk =
    tag:
    let
      r = {
        _type = "option-type";
        name = "gauge";
        nestedTypes = { };
        description = r;
        check = v: v == tag;
      };
    in
    r;
  g = mk 1;
in
{
  flake.tests.types-identity.test-compared-regime-decides-across-a-back-edge = {
    expr = {
      synthetic = t.typeEq g (mk 2);
      syntheticSelf = t.typeEq g g;
      port = t.typeEq ft.port u.port;
      intsBetween = t.typeEq (ft.ints.between 0 1) (u.ints.between 0 1);
      nonEmptyStr = t.typeEq ft.nonEmptyStr u.nonEmptyStr;
      listOfPort = t.typeEq (ft.listOf ft.port) (u.listOf u.port);
      portSelf = t.typeEq ft.port ft.port;
      derivedDiffers = t.typeEq (ft.port // { description = "a"; }) (ft.port // { description = "b"; });
      shallowCopy = t.typeEq ft.port (ft.port // { });
    };
    expected = {
      synthetic = false;
      syntheticSelf = true;
      port = false;
      intsBetween = false;
      nonEmptyStr = false;
      listOfPort = false;
      portSelf = true;
      derivedDiffers = false;
      shallowCopy = true;
    };
  };
}
