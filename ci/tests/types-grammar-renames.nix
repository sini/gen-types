# The grammar's L1 renames here (den-hoag-7gp66 O4, R10 rule 3): `listOf`/`attrsOf`/`option` are
# `checkedListOf`/`checkedAttrsOf`/`checkedOption`. The old names refuse catchably (the message is
# pinned by the generated `root-surface-retired.*` cells), and each successor is the same
# construction: it accepts and refuses what the old name did, and mints under the same constructor.
{ genTypes, ... }:
let
  t = genTypes;
  refuses = v: !(builtins.tryEval (builtins.typeOf v)).success;
  # agree on one input, differ on a control input
  serves = ty: ok: bad: [
    (ty.verify ok == null)
    (ty.verify bad == null)
  ];
in
{
  flake.tests.types-grammar-renames.test-old-names-refuse = {
    expr = map refuses [
      t.listOf
      t.attrsOf
      t.option
    ];
    expected = [
      true
      true
      true
    ];
  };

  flake.tests.types-grammar-renames.test-successors-serve = {
    expr = {
      listOf = serves (t.checkedListOf t.int) [ 1 ] [ "a" ];
      attrsOf = serves (t.checkedAttrsOf t.int) { a = 1; } { a = "a"; };
      option = serves (t.checkedOption t.int) null "a";
      ctors = map (ty: (t.payloadOf ty).ctor) [
        (t.checkedListOf t.int)
        (t.checkedAttrsOf t.int)
        (t.checkedOption t.int)
      ];
    };
    expected = {
      listOf = [
        true
        false
      ];
      attrsOf = [
        true
        false
      ];
      option = [
        true
        false
      ];
      ctors = [
        "listOf"
        "attrsOf"
        "option"
      ];
    };
  };
}
