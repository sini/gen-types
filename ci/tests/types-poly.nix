# gen-types: polymorphic combinators — option/listOf/attrsOf/union/intersection/
# enum/tuple/optionalAttr, incl. nested composition and error-context threading.
{ genTypes, ... }:
let
  t = genTypes;

  # A stand-in for a merge strategy: a type record with a name and a domain predicate and NO
  # `verify` -- the shape of every gen-merge structural type, kept local so this suite needs no
  # gen-merge input.
  strategy = {
    name = "strategy";
    admits = _: true;
  };
  evaluates = e: (builtins.tryEval (builtins.deepSeq e e)).success;
  # every member-reading combinator over `m`, with a value the stand-in's domain would admit
  over = m: {
    option = (t.option m).verify 1;
    listOf = (t.listOf m).verify [ 1 ];
    listOfEmpty = (t.listOf m).verify [ ];
    attrsOf = (t.attrsOf m).verify { x = 1; };
    union =
      (t.union [
        m
        t.str
      ]).verify
        1;
    unionOrder =
      (t.union [
        t.str
        m
      ]).verify
        "hello";
    intersection =
      (t.intersection [
        m
        t.any
      ]).verify
        1;
    tuple = (t.tuple [ m ]).verify [ 1 ];
    struct = (t.struct "s" { x = m; }).verify { x = 1; };
    structMissingKey = (t.struct "s" { x = m; }).verify { };
    optionalAttr = (t.struct "s" { x = t.optionalAttr m; }).verify { x = 1; };
    refined = (t.refined m [ ]).verify 1;
  };
in
{
  # ── option ──
  flake.tests.types-poly.test-option-null = {
    expr = (t.option t.int).verify null;
    expected = null;
  };
  flake.tests.types-poly.test-option-value-ok = {
    expr = (t.option t.int).verify 3;
    expected = null;
  };
  flake.tests.types-poly.test-option-value-fail = {
    expr = (t.option t.int).verify "x";
    expected = "in option<int>: expected type 'int' but value \"x\" is of type 'string'";
  };

  # ── listOf ──
  flake.tests.types-poly.test-listOf-ok = {
    expr = (t.listOf t.int).verify [
      1
      2
      3
    ];
    expected = null;
  };
  flake.tests.types-poly.test-listOf-empty-ok = {
    expr = (t.listOf t.int).verify [ ];
    expected = null;
  };
  flake.tests.types-poly.test-listOf-element-fail = {
    expr = (t.listOf t.int).verify [
      1
      "x"
    ];
    expected = "in listOf<int> element: expected type 'int' but value \"x\" is of type 'string'";
  };
  flake.tests.types-poly.test-listOf-not-a-list = {
    expr = (t.listOf t.int).verify 5;
    expected = "expected type 'listOf<int>' but value 5 is of type 'int'";
  };

  # ── attrsOf ──
  flake.tests.types-poly.test-attrsOf-ok = {
    expr = (t.attrsOf t.int).verify {
      a = 1;
      b = 2;
    };
    expected = null;
  };
  flake.tests.types-poly.test-attrsOf-value-fail = {
    expr = (t.attrsOf t.int).verify {
      a = 1;
      b = "x";
    };
    expected = "in attrsOf<int> value: expected type 'int' but value \"x\" is of type 'string'";
  };
  flake.tests.types-poly.test-attrsOf-not-attrs = {
    expr = (t.attrsOf t.int).verify [ 1 ];
    expected = "expected type 'attrsOf<int>' but value [ … (1 element) ] is of type 'list'";
  };

  # ── union ──
  flake.tests.types-poly.test-union-first-ok = {
    expr =
      (t.union [
        t.int
        t.str
      ]).verify
        5;
    expected = null;
  };
  flake.tests.types-poly.test-union-second-ok = {
    expr =
      (t.union [
        t.int
        t.str
      ]).verify
        "hi";
    expected = null;
  };
  flake.tests.types-poly.test-union-none-fail = {
    expr =
      (t.union [
        t.int
        t.str
      ]).verify
        true;
    expected = "expected type 'union<int,string>' but value true is of type 'bool'";
  };

  # ── intersection ──
  flake.tests.types-poly.test-intersection-ok = {
    expr =
      (t.intersection [
        t.int
        t.number
      ]).verify
        5;
    expected = null;
  };
  flake.tests.types-poly.test-intersection-first-fail = {
    expr =
      (t.intersection [
        t.int
        t.number
      ]).verify
        "x";
    expected = "in intersection<int,number>: expected type 'int' but value \"x\" is of type 'string'";
  };

  # ── enum ──
  flake.tests.types-poly.test-enum-ok = {
    expr =
      (t.enum "color" [
        "red"
        "green"
      ]).verify
        "red";
    expected = null;
  };
  flake.tests.types-poly.test-enum-fail = {
    expr =
      (t.enum "color" [
        "red"
        "green"
      ]).verify
        "blue";
    expected = "\"blue\" is not a member of enum 'color'";
  };

  # ── tuple ──
  flake.tests.types-poly.test-tuple-ok = {
    expr =
      (t.tuple [
        t.int
        t.str
      ]).verify
        [
          1
          "a"
        ];
    expected = null;
  };
  flake.tests.types-poly.test-tuple-element-fail = {
    expr =
      (t.tuple [
        t.int
        t.str
      ]).verify
        [
          1
          2
        ];
    expected = "in tuple<int, string>: in element 1: expected type 'string' but value 2 is of type 'int'";
  };
  flake.tests.types-poly.test-tuple-wrong-length = {
    expr =
      (t.tuple [
        t.int
        t.str
      ]).verify
        [ 1 ];
    expected = "expected tuple of length 2 but value [ … (1 element) ] has length 1";
  };
  flake.tests.types-poly.test-tuple-not-a-list = {
    expr =
      (t.tuple [
        t.int
        t.str
      ]).verify
        5;
    expected = "expected type 'tuple<int, string>' but value 5 is of type 'int'";
  };

  # ── optionalAttr ──
  flake.tests.types-poly.test-optionalAttr-ok = {
    expr = (t.optionalAttr t.int).verify 3;
    expected = null;
  };
  flake.tests.types-poly.test-optionalAttr-fail = {
    expr = (t.optionalAttr t.int).verify "x";
    expected = "in optionalAttr<int>: expected type 'int' but value \"x\" is of type 'string'";
  };
  flake.tests.types-poly.test-optionalAttr-basename = {
    expr = (t.optionalAttr t.int).__name;
    expected = "optionalAttr";
  };

  # ── nested composition ──
  flake.tests.types-poly.test-nested-listOf-option = {
    expr = (t.listOf (t.option t.int)).verify [
      1
      null
      2
    ];
    expected = null;
  };
  flake.tests.types-poly.test-nested-attrsOf-listOf-fail = {
    expr = (t.attrsOf (t.listOf t.int)).verify {
      a = [
        1
        "x"
      ];
    };
    expected = "in attrsOf<listOf<int>> value: in listOf<int> element: expected type 'int' but value \"x\" is of type 'string'";
  };

  # ── a member that is not a checker ──
  # Each combinator directly holding a member with no `verify` refuses catchably, on every value
  # and in every member order (the refusal's message is pinned in ../tests-error.nix).
  flake.tests.types-poly.test-cyiuz-a-member-without-verify-is-refused-catchably = {
    expr = builtins.mapAttrs (_: evaluates) (over strategy);
    expected = builtins.mapAttrs (_: _: false) (over strategy);
  };
  # control: the same combinators over a checker answer (null or an error string)
  flake.tests.types-poly.test-cyiuz-control-checker-member-answers = {
    expr = builtins.mapAttrs (_: evaluates) (over t.int);
    expected = builtins.mapAttrs (_: _: true) (over t.int);
  };
  # The member check runs at USE, not when the combinator is applied: a self-referential type
  # answers, where a formation-time check would diverge.
  flake.tests.types-poly.test-cyiuz-recursive-type-answers-at-use =
    let
      r = t.union [
        t.int
        (t.listOf r)
      ];
    in
    {
      expr = r.verify [
        1
        [
          2
          [ 3 ]
        ]
      ];
      expected = null;
    };
}
