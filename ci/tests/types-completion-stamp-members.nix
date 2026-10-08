# gen-types: a composite over a `//` copy (den-hoag-6d5r3). A composite's mark is minted over one tag
# per member, so a member departing from the record its completion returned (`stampHolds`, over every
# field: gen-types' checkers state no `__stampReads`) enters SEALED, and the composite carries no
# identity a demand could take for the composite over the base. The stamp is read only of a minted member.
{ genTypes, ... }:
let
  t = genTypes;
  refused = e: !(builtins.tryEval (builtins.deepSeq e e)).success;
  copy = t.int // {
    verify = _: null;
  };
  composites = {
    checkedListOf = t.checkedListOf;
    checkedAttrsOf = t.checkedAttrsOf;
    checkedOption = t.checkedOption;
    union =
      m:
      t.union [
        m
        t.bool
      ];
    tuple = m: t.tuple [ m ];
    optionalAttr = t.optionalAttr;
    nested = m: t.checkedListOf (t.checkedListOf m);
  };
in
{
  flake.tests.types-completion-stamp-members = {
    # RED before: every row read `{ refused = false; sealed = [ ]; sameAsBase = true; }`, the
    # composite carrying the identity of the composite over `int`
    test-a-composite-over-a-copy-has-no-identity = {
      expr = builtins.mapAttrs (_: c: {
        refused = refused (t.idOf (c copy));
        sealed = builtins.attrNames (c copy).__sealed != [ ];
        sameAsBase = (builtins.tryEval (t.typeEq (c copy) (c t.int))).value or false;
      }) composites;
      expected = builtins.mapAttrs (_: _: {
        refused = true;
        sealed = true;
        sameAsBase = false;
      }) composites;
    };
    # THE PRICE, carried: a description-only copy is refused as a member as it is alone
    test-a-description-only-member-pays-the-price = {
      expr = refused (t.idOf (t.checkedListOf (t.int // { description = "an integer"; })));
      expected = true;
    };
    # Controls: over a completed record each composite keeps its identity, and `// { }` is no copy
    test-completed-members-keep-their-identity = {
      expr = builtins.mapAttrs (_: c: [
        (refused (t.idOf (c t.int)))
        (t.idOf (c (t.int // { })) == t.idOf (c t.int))
      ]) composites;
      expected = builtins.mapAttrs (_: _: [
        false
        true
      ]) composites;
    };
  };
}
