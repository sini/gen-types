# gen-types: the construction-payload read surface — `__payload` on every checker, read through
# `payloadOf`, which answers only where the payload re-mints to the digest the record carries.
# RED before the surface landed: no checker carried `__payload` and no published name read one.
{ genTypes, ... }:
let
  t = genTypes;
  refused = v: !(builtins.tryEval (builtins.deepSeq v v)).success;
  sealed = t.typedef' "t" (_: null);
  cyc =
    let
      r = t.union [
        t.str
        (t.listOf r)
      ];
    in
    r;
in
{
  flake.tests.types-payload.test-payloadOf-answers-the-minted-construction = {
    expr = {
      enum = t.payloadOf (t.enum "e" [ "a" ]);
      prim = t.payloadOf t.int;
      # a composite's arguments hold member IDENTITIES, never member checkers
      listOf =
        t.payloadOf (t.listOf t.int) == {
          ctor = "listOf";
          args = t.int.__mint.minted;
        };
    };
    expected = {
      enum = {
        ctor = "enum";
        args = {
          name = "e";
          elems = [ "a" ];
        };
      };
      prim = {
        ctor = "prim";
        args = "int";
      };
      listOf = true;
    };
  };

  # The certification: a payload is readable only as the preimage of the record's OWN digest. The
  # planted row hands `int` an enum's payload, which the reader would answer for `int` if the
  # re-mint comparison were deleted; `int` itself is the live control on the same reader.
  flake.tests.types-payload.test-payloadOf-refuses-everything-it-cannot-certify = {
    expr = {
      control = refused (t.payloadOf t.int);
      planted = refused (t.payloadOf (t.int // { inherit (t.enum "e" [ "a" ]) __payload; }));
      refined = refused (t.payloadOf (t.refined t.int t.refinements.positive));
      typedef = refused (t.payloadOf sealed);
      cyclic = refused (t.payloadOf cyc);
      foreign = refused (t.payloadOf { name = "x"; });
      notAttrs = refused (t.payloadOf 1);
    };
    expected = {
      control = false;
      planted = true;
      refined = true;
      typedef = true;
      cyclic = true;
      foreign = true;
      notAttrs = true;
    };
  };

  # The field is TOTAL and TAGGED like `__mint`, and the sealed arm never carries `args`. A type
  # with a SEALED COMPONENT is minted, and its payload holds `sealedMarker` where the component sits,
  # never the lambda (`payloadOf` still refuses it, above).
  flake.tests.types-payload.test-payload-field-is-total-and-tagged = {
    expr = {
      minted = builtins.attrNames (t.enum "e" [ "a" ]).__payload;
      sealed = sealed.__payload.minted.args;
      refined = (t.refined t.int t.refinements.positive).__payload.minted.args.refinements;
      cyclicKeys = builtins.attrNames cyc.__payload;
    };
    expected = {
      minted = [ "minted" ];
      sealed = {
        name = "t";
        verify.sealed = true;
      };
      refined = [
        {
          check.sealed = true;
          message = "must be positive";
        }
      ];
      cyclicKeys = [ "unmintable" ];
    };
  };

  # The field joins the COMPARED regime's subject and must not detonate it: a sealed record still
  # equals itself, a minted-vs-sealed pair and a cyclic self stay as before, and two separately
  # written verifiers under one name are refused by name (one mark, unequal only at a lambda).
  flake.tests.types-payload.test-payload-field-leaves-the-compared-regime-intact = {
    expr = {
      sealedSelf = t.typeEq sealed sealed;
      sealedTwin = refused (t.typeEq sealed (t.typedef' "t" (_: null)));
      mintedVsSealed = t.typeEq (t.enum "t" [ "a" ]) sealed;
      cyclicSelf = t.typeEq cyc cyc;
    };
    expected = {
      sealedSelf = true;
      sealedTwin = true;
      mintedVsSealed = false;
      cyclicSelf = true;
    };
  };
}
