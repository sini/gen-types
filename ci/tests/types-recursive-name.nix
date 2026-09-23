# A self-referential type's NAME is finite, so its refusal returns (ADR-0025 item 1): a composite
# name is rendered within `renderBudget` bytes handed down in preorder (lib/checkers.nix,
# `renderNode`). On the tree before it, every refusal below diverged uncatchably.
{ genTypes, ... }:
let
  t = genTypes;
  inherit (t)
    int
    list
    union
    listOf
    attrsOf
    option
    tuple
    intersection
    struct
    enum
    refined
    ;
  N = k: builtins.concatStringsSep "" (builtins.genList (_: "n") k);
  r = union [
    int
    (listOf r)
  ];
  r3 = union [
    int
    (listOf r3)
    (attrsOf r3)
    (listOf (listOf r3))
  ];
  l = listOf l;
  o = option (listOf o);
  a = attrsOf (union [
    int
    a
  ]);
  tu = tuple [
    int
    (option tu)
  ];
  i = intersection [
    list
    (listOf (option i))
  ];
  rf = refined (listOf (option rf)) [ ];
  # a hand-built member: a string name, a verify, and no renderer of its own
  foreign = {
    name = N 300;
    verify = _: null;
  };
  hasPrefix = p: s: builtins.substring 0 (builtins.stringLength p) s == p;
  hasSuffix =
    x: s:
    let
      n = builtins.stringLength s;
      m = builtins.stringLength x;
    in
    n >= m && builtins.substring (n - m) m s == x;
  m = r.verify "a";
  # a flat union of the given member names
  flat = ns: union (map (n: enum n [ 1 ]) ns);
in
{
  flake.tests.types-recursive-name.test-self-referential-union-refusal-returns = {
    expr =
      hasPrefix "expected type 'union<int,listOf<union<int,listOf<" m
      && hasSuffix ">' but value \"a\" is of type 'string'" m
      && builtins.length (builtins.split "…" m) == 3;
    expected = true;
  };
  flake.tests.types-recursive-name.test-self-referential-check-refuses-catchably = {
    expr =
      (builtins.tryEval (
        r.check [
          1
          [ "a" ]
        ] null
      )).success;
    expected = false;
  };
  flake.tests.types-recursive-name.test-every-combinator-self-reference-refuses = {
    expr = map builtins.isString [
      (l.verify 5)
      (o.verify 5)
      (a.verify 5)
      (tu.verify [
        1
        [
          2
          5
        ]
      ])
      (i.verify 5)
      (rf.verify 5)
      (r3.verify "a")
    ];
    expected = [
      true
      true
      true
      true
      true
      true
      true
    ];
  };
  flake.tests.types-recursive-name.test-struct-missing-key-over-self-referential-member = {
    expr = (struct "x" { a = r; }).verify { };
    expected = "in struct 'x': missing member 'a'";
  };
  flake.tests.types-recursive-name.test-branching-self-reference-name-within-budget = {
    expr = builtins.stringLength r3.name <= 256;
    expected = true;
  };
  # `refined` over a base with no renderer is bounded like a member held directly
  flake.tests.types-recursive-name.test-refined-over-foreign-base-name-within-budget = {
    expr = map (x: builtins.stringLength x.name <= 256) [
      (refined foreign [ ])
      (union [
        int
        (refined foreign [ ])
      ])
    ];
    expected = [
      true
      true
    ];
  };
  # the boundary: 253 B with 1-byte trailing members fits the reservation and is whole; 256 B whose
  # trailing member is shorter than the elision mark does not, and elides the member before it
  flake.tests.types-recursive-name.test-boundary-253-bytes-is-whole = {
    expr =
      (flat [
        (N 242)
        "a"
        "b"
      ]).name;
    expected = "union<${N 242},a,b>";
  };
  flake.tests.types-recursive-name.test-boundary-256-bytes-short-trailer-elides = {
    expr =
      (flat [
        (N 247)
        "e"
      ]).name;
    expected = "union<…,e>";
  };
  # controls: the accept path, and names under the budget, are unchanged
  flake.tests.types-recursive-name.test-control-self-referential-accepts = {
    expr = r.verify [
      1
      [
        2
        [ 3 ]
      ]
    ];
    expected = null;
  };
  flake.tests.types-recursive-name.test-control-name-under-budget-is-whole = {
    expr = (union (builtins.genList (k: enum "e${toString k}" [ k ]) 40)).name;
    expected = "union<${builtins.concatStringsSep "," (builtins.genList (k: "e${toString k}") 40)}>";
  };
}
