# gen-types: an `addCheck`-wrapped REGISTRY LEAF keeps its base's `name`, `nestedTypes` and `functor`,
# so the leaf registry alone minted it as the leaf. Its added predicate is a lambda and cannot enter
# the mint, so it must fall to the COMPARED regime (ADR-0034) instead of collapsing. RED before the
# reflexivity conjunct in `mintForeign`: `pair`, `againstLeaf`, `inComposite` and `rawOverride` read
# `true`.
{ genTypes, lib, ... }:
let
  t = genTypes;
  ft = lib.types;
  p = s: s != "a";
  q = s: s != "b";
  a = ft.addCheck ft.str p;
  b = ft.addCheck ft.str q;
  registry = [
    "str"
    "int"
    "bool"
    "float"
    "anything"
    "raw"
    "unspecified"
    "attrs"
    "package"
  ];
  # Two SEPARATE `listOf` constructions per registry name. The `mk` indirection keeps the two calls
  # from being one shared thunk, so a sealed leaf compares two distinct records and answers `false`;
  # comparing `ft.${n}` with itself would take the pointer shortcut and stay `true` whatever the
  # leaf's regime.
  mk = f: f 0;
  twins =
    types:
    map (n: t.typeEq (mk (_: types.listOf types.${n})) (mk (_: types.listOf types.${n}))) registry;
  # The planted red fixture: a lib whose registry leaf `str` is NOT reflexive. Under the conjunct it
  # must seal, and the twins row must see that.
  planted =
    (lib.extend (
      _: prev: {
        types = prev.types // {
          str = prev.types.str // {
            functor = prev.types.str.functor // {
              type = null;
            };
          };
        };
      }
    )).types;
in
{
  flake.tests.types-identity.test-foreign-addCheck-registry-leaf-does-not-silently-unify = {
    expr = {
      fixtureDiscriminates = [
        (a.check "a")
        (b.check "a")
      ];
      pair = t.typeEq a b;
      againstLeaf = t.typeEq a ft.str;
      inComposite = t.typeEq (ft.listOf a) (ft.listOf b);
      rawOverride = t.typeEq (ft.str // { check = s: s == "x"; }) ft.str;
      sameBinding = t.typeEq a a;
      leafUnchanged = t.typeEq ft.str ft.str;
      listOfStrSeparateBuild = t.typeEq (ft.listOf ft.str) (ft.listOf ft.str);
      # Every registry leaf still mints: its separately built `listOf` twins still unify.
      everyRegistryLeafStillMints = twins ft;
      # The same row over the planted non-reflexive `str`: the discriminating twin of the row above.
      plantedNonReflexiveLeafSeals = twins planted;
    };
    expected = {
      fixtureDiscriminates = [
        false
        true
      ];
      pair = false;
      againstLeaf = false;
      inComposite = false;
      rawOverride = false;
      sameBinding = true;
      leafUnchanged = true;
      listOfStrSeparateBuild = true;
      everyRegistryLeafStillMints = [
        true
        true
        true
        true
        true
        true
        true
        true
        true
      ];
      plantedNonReflexiveLeafSeals = [
        false
        true
        true
        true
        true
        true
        true
        true
        true
      ];
    };
  };
}
