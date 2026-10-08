# gen-types: the completion stamp (gate C3). A type's mark is a claim about the record its constructor
# completed; a `//` copy keeps the mark and its witness, and `typeEq` refuses it by name.
{ genTypes, ... }:
let
  t = genTypes;
  refused = e: !(builtins.tryEval (builtins.deepSeq e e)).success;
in
{
  flake.tests.types-completion-stamp = {
    # The silent identity defect: a `//` that replaces `verify` kept `int`'s mark and was `true`.
    test-a-slash-copy-is-refused-by-name = {
      expr = {
        slashVerify = refused (t.typeEq t.int (t.int // { verify = _: null; }));
        stampOk = t.stampOk (t.int // { verify = _: null; });
        # the copy still serves values as a checker; only the identity comparison refuses
        copyVerifies = (t.int // { verify = _: null; }).verify "x";
      };
      expected = {
        slashVerify = true;
        stampOk = false;
        copyVerifies = null;
      };
    };
    # THE PRICE, stated and pinned: a description-only `//` (the nixpkgs idiom) is a copy too.
    test-a-description-only-copy-pays-the-price = {
      expr = refused (t.typeEq t.int (t.int // { description = "an integer"; }));
      expected = true;
    };
    # Controls: every completed record passes, through every constructor that completes one.
    test-completed-records-pass = {
      expr = {
        prim = t.typeEq t.int t.int;
        composite = t.typeEq (t.checkedListOf t.int) (t.checkedListOf t.int);
        structOverride = t.typeEq ((t.struct "s" { a = t.int; }).override { total = false; }) (
          (t.struct "s" { a = t.int; }).override { total = false; }
        );
        refined =
          let
            x = t.refined t.int t.refinements.positive;
          in
          t.typeEq x x;
        distinct = t.typeEq t.int t.str;
        stampOk = builtins.all t.stampOk [
          t.int
          (t.checkedListOf t.str)
          (t.refined t.int t.refinements.positive)
          (t.struct "s" { a = t.int; })
          { name = "foreign"; }
        ];
      };
      expected = {
        prim = true;
        composite = true;
        structOverride = true;
        refined = true;
        distinct = false;
        stampOk = true;
      };
    };
  };
}
