# A self-referential or over-deep type has NO IDENTITY, and says so catchably (ADR-0034's excluded
# populations): the step-indexed guard in lib/checkers.nix (`identityGuard`) tags it `unmintable`,
# `typeEq` decides over the record, and demanding `__id` is the named refusal. On the tree before it,
# every cycle below re-entered its own memoised mint (an uncatchable `infinite recursion`) and the
# 1000-deep chain overflowed the stack.
{ genTypes, ... }:
let
  inherit (genTypes)
    int
    str
    list
    union
    listOf
    attrsOf
    option
    tuple
    intersection
    optionalAttr
    struct
    refined
    typeEq
    ;
  tag = v: if v.__mint ? minted then "minted" else "unmintable:${v.__mint.unmintable.ctor}";
  r = union [
    int
    (listOf r)
  ];
  r' = union [
    int
    (listOf r')
  ];
  s = struct "s" { next = option s; };
  holder = listOf r;
  flat = union [
    int
    (listOf int)
  ];
  chain = n: if n == 0 then int else listOf (chain (n - 1));
  dag =
    n:
    if n == 0 then
      int
    else
      let
        p = dag (n - 1);
      in
      union [
        p
        p
      ];
in
{
  # every composite constructor closing a cycle; the tag is the OUTERMOST constructor's
  flake.tests.types-recursive-identity.test-every-constructor-cycle-is-unmintable = {
    expr =
      let
        l = listOf l;
        a = attrsOf (union [
          int
          a
        ]);
        st = struct "st" { next = option (listOf st); };
        t = tuple [
          int
          (option t)
        ];
        i = intersection [
          list
          (listOf (option i))
        ];
        oa = struct "oa" { x = optionalAttr (listOf oa); };
        rf = refined (listOf (option rf)) [ ];
        r2 = union [
          int
          (listOf r2)
          (attrsOf r2)
        ];
      in
      map tag [
        r
        l
        a
        st
        s
        t
        i
        oa
        rf
        holder
        r2
      ];
    expected = [
      "unmintable:union"
      "unmintable:listOf"
      "unmintable:attrsOf"
      "unmintable:struct"
      "unmintable:struct"
      "unmintable:tuple"
      "unmintable:intersection"
      "unmintable:struct"
      "unmintable:refined"
      "unmintable:listOf"
      "unmintable:union"
    ];
  };
  flake.tests.types-recursive-identity.test-demanding-a-cyclic-identity-refuses-catchably = {
    expr = map (v: (builtins.tryEval v.__id).success) [
      r
      s
      holder
    ];
    expected = [
      false
      false
      false
    ];
  };
  # deciding is not demanding: the COMPARED arm answers, finer than the name
  flake.tests.types-recursive-identity.test-a-cyclic-type-is-decided = {
    expr = {
      self = typeEq r r;
      twin = typeEq r r';
      againstInt = typeEq r int;
      nominal = typeEq s s;
      holder = typeEq holder holder;
    };
    expected = {
      self = true;
      twin = false;
      againstInt = false;
      nominal = true;
      holder = true;
    };
  };
  # the bound: 128 levels mint, 129 refuse, and a 1000-deep chain refuses rather than overflowing
  flake.tests.types-recursive-identity.test-depth-bound = {
    expr = map (n: tag (chain n)) [
      128
      129
      1000
    ];
    expected = [
      "minted"
      "unmintable:listOf"
      "unmintable:listOf"
    ];
  };
  # linear under sharing: `dag 128` expands to 2^128 leaves and still mints; an unmemoised guard
  # would pay the expansion
  flake.tests.types-recursive-identity.test-shared-dag-mints-to-the-bound = {
    expr = map (n: tag (dag n)) [
      20
      128
      129
    ];
    expected = [
      "minted"
      "minted"
      "unmintable:union"
    ];
  };
  # controls: an acyclic type's digest does not move, its accept path is unchanged, and the guard
  # lives on composites only
  flake.tests.types-recursive-identity.test-control-acyclic-digests-unchanged = {
    expr = {
      flat = flat.__id;
      int = int.__id;
      rebuild = typeEq flat (union [
        int
        (listOf int)
      ]);
      differs = typeEq flat (union [
        str
        (listOf int)
      ]);
    };
    expected = {
      flat = "type:493b8fd2b1fa62b9d7abd48902717b1b1747f406ef6633d7be402d9df7295856";
      int = "type:d56681ac4aa3f64b427f9aceaab601fa2fe1e0db2cce50349be86f3fa0d886b6";
      rebuild = true;
      differs = false;
    };
  };
  flake.tests.types-recursive-identity.test-control-cyclic-type-accepts = {
    expr = r.verify [
      1
      [
        2
        [ 3 ]
      ]
    ];
    expected = null;
  };
  # the guard is total: a deep force of an acyclic composite, and of a cycle's own guard, terminates
  flake.tests.types-recursive-identity.test-guard-survives-a-deep-force = {
    expr = {
      acyclic = builtins.deepSeq (listOf (option int)) true;
      cyclicGuard = builtins.deepSeq r.__okAt true;
    };
    expected = {
      acyclic = true;
      cyclicGuard = true;
    };
  };
  flake.tests.types-recursive-identity.test-control-guard-on-composites-only = {
    expr = {
      leaf = int ? __okAt;
      composite = (listOf int) ? __okAt;
    };
    expected = {
      leaf = false;
      composite = true;
    };
  };
}
