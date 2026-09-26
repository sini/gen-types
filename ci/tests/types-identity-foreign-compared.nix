# gen-types: a FOREIGN option-type record is compared, never minted from its name (ADR-0034). A
# record's `name` and `nestedTypes` claim a constructor without declaring one, and three shapes carry
# another type's name and structure with a different check: an `addCheck`'d `int` installed at
# `types.int` by `lib.extend` (reflexive, because `functor.type` is a late-bound name lookup), a
# record whose `functor.type` is itself (gen-merge `exportType`'s shape), and a composite `addCheck`
# or nixpkgs' own `nonEmptyListOf`, whose `.name` is `listOf`. RED before the foreign branch stopped
# minting: every `defects` entry reads `true`.
{ genTypes, lib, ... }:
let
  t = genTypes;
  ft = lib.types;
  install =
    f:
    (lib.extend (
      _: p: {
        types = p.types // {
          int = p.types.addCheck p.types.int f;
        };
      }
    )).types;
  pt = install (v: v > 5);
  qt = install (v: v < 3);
  self =
    c:
    let
      r = {
        _type = "option-type";
        name = "int";
        nestedTypes = { };
        functor = {
          name = "int";
          type = r;
          payload = null;
          binOp = _: _: null;
        };
        check = c;
      };
    in
    r;
  sA = self (v: v < 10);
  sB = self (v: v > 100);
  x = ft.listOf ft.str;
in
{
  flake.tests.types-identity.test-foreign-record-is-compared-never-minted-by-name = {
    expr = {
      fixturesDiscriminate = [
        (pt.int.check 1)
        (qt.int.check 1)
        (sA.check 5)
        (sB.check 5)
        ((ft.nonEmptyListOf ft.str).check [ ])
        (x.check [ ])
      ];
      defects = {
        installedVsStock = t.typeEq pt.int ft.int;
        installedPair = t.typeEq pt.int qt.int;
        installedInListOf = t.typeEq (pt.listOf pt.int) (ft.listOf ft.int);
        selfReflexivePair = t.typeEq sA sB;
        selfReflexiveVsStock = t.typeEq sA ft.int;
        compositeAddCheck = t.typeEq (ft.addCheck x (xs: xs != [ ])) x;
        nonEmptyListOf = t.typeEq (ft.nonEmptyListOf ft.str) x;
      };
      controls = {
        stockSelf = t.typeEq ft.int ft.int;
        sharedInstalled = t.typeEq pt.int pt.int;
        sharedSelfReflexive = t.typeEq sA sA;
        sharedComposite = t.typeEq x x;
        shallowCopy = t.typeEq ft.port (ft.port // { });
        differentElem = t.typeEq (ft.listOf ft.str) (ft.listOf ft.int);
      };
    };
    expected = {
      fixturesDiscriminate = [
        false
        true
        true
        false
        false
        true
      ];
      defects = {
        installedVsStock = false;
        installedPair = false;
        installedInListOf = false;
        selfReflexivePair = false;
        selfReflexiveVsStock = false;
        compositeAddCheck = false;
        nonEmptyListOf = false;
      };
      controls = {
        stockSelf = true;
        sharedInstalled = true;
        sharedSelfReflexive = true;
        sharedComposite = true;
        shallowCopy = true;
        differentElem = false;
      };
    };
  };
}
