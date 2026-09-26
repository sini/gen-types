# gen-types: an `addCheck`-wrapped leaf keeps its base's `name`, `nestedTypes` and `functor`, so a
# mint over those claimed it was the leaf. Its added predicate is a lambda and cannot enter a mint,
# so it is decided in the COMPARED regime (ADR-0034), as every foreign record now is. RED under the
# registry mint without a reflexivity conjunct: `pair`, `againstLeaf`, `inComposite` and
# `rawOverride` read `true`.
{ genTypes, lib, ... }:
let
  t = genTypes;
  ft = lib.types;
  p = s: s != "a";
  q = s: s != "b";
  a = ft.addCheck ft.str p;
  b = ft.addCheck ft.str q;
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
      sharedListOf =
        let
          x = ft.listOf ft.str;
        in
        t.typeEq x x;
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
      sharedListOf = true;
    };
  };
}
