# gen-types — pure structural type CHECKERS.
#
# The checking half of a pure Nix module system: a value either satisfies a type
# (verify => null) or it does not (verify => an error string). This is contract
# checking in the sense of § Findler & Felleisen 2002 — a type is a boundary that
# blames the value on mismatch — restricted to a first-order, allocation-frugal
# core so it stays a single eval pass on the happy path.
#
# Every checker is a record { name; verify; check; __name; __mint; __id; }:
#   name    — full structural name, e.g. "listOf<int>"
#   verify  — value -> null | errString   (null = ok)
#   check   — v: v2: throws verify's error on failure, returns v2 on success
#   __name  — base name with polymorphic metadata stripped ("listOf")
#   __mint  — the identity REGIME as a tagged sum, minted over the CONSTRUCTION rather
#             than over the name: { minted = "type:<digest>"; } where the constructor's
#             arguments are inert, { unmintable = { ctor; reason; }; } where one of them
#             is a caller-supplied lambda. This is what the equality relation reads.
#   __id    — the accessor for a consumer that DEMANDS an identity: the minted value, or
#             the mint's own named refusal. Lazy, and never what the relation reads.
#
# NO nixpkgs.lib here (purity invariant, see ci/tests/types-purity.nix): builtins
# plus the handful of gen-prelude utilities the substrate already vendors.
{ prelude, identity }:
let
  inherit (prelude)
    all
    any
    attrNames
    attrValues
    concatStringsSep
    elem
    elemAt
    fix
    head
    length
    map
    mapAttrs
    optional
    ;
  inherit (builtins)
    isFloat
    isInt
    isPath
    removeAttrs
    split
    tryEval
    typeOf
    ;
  # prelude re-exports these three; taken from builtins keeps the primitive
  # predicates grouped with the rest of builtins.is*.
  inherit (builtins)
    isAttrs
    isBool
    isFunction
    isList
    isString
    ;
  isNull = v: v == null;
  isDerivation = v: isAttrs v && (v.type or null) == "derivation";

  # ── error rendering (only ever forced on the failure path) ──

  # Minimal value pretty-printer. Never invoked on a successful verify, so its
  # cost does not touch the happy path. Pure builtins — no lib.generators.
  toPretty =
    v:
    if isString v then
      ''"${v}"''
    else if isInt v || isFloat v then
      toString v
    else if isBool v then
      (if v then "true" else "false")
    else if isNull v then
      "null"
    else if isPath v then
      toString v
    else if isFunction v then
      "«lambda»"
    else if isDerivation v then
      "«derivation ${v.name or "?"}»"
    else if isList v then
      "[ ${concatStringsSep " " (map toPretty v)} ]"
    else if isAttrs v then
      "{ ${concatStringsSep " " (map (n: "${n} = ${toPretty v.${n}};") (attrNames v))} }"
    else
      typeOf v;

  typeError = name: v: "expected type '${name}' but value ${toPretty v} is of type '${typeOf v}'";

  # Thread an enclosing frame onto a nested error; null propagates unchanged.
  addContext = context: error: if error == null then null else "${context}: ${error}";

  joinKeys = list: concatStringsSep ", " (map (e: "'${e}'") list);

  # ── single-pass / rescan-on-failure primitives (§ design requirement) ──
  #
  # Happy path: `all` runs the predicate over each element exactly once and
  # short-circuits to null. Only when a failure is known do we re-scan to LOCATE
  # the first offending element and materialize its message — the success path
  # is never double-costed.
  firstError =
    f: xs:
    if all (x: f x == null) xs then
      null
    else
      let
        recur =
          i:
          let
            e = f (elemAt xs i);
          in
          if e != null then e else recur (i + 1);
      in
      recur 0;

  # Same shape but over a fixed list of verifier closures applied to one value.
  firstFailing =
    funcs: v:
    if all (f: f v == null) funcs then
      null
    else
      let
        recur =
          i:
          let
            e = (elemAt funcs i) v;
          in
          if e != null then e else recur (i + 1);
      in
      recur 0;

  # ── identity ──
  baseName = name: head (split "<" name);

  # ★ THE MINT IS THE SUBSTRATE'S, NOT THIS LIBRARY'S. `mkId` was a SECOND hashing surface —
  # `hashString "sha256" "gen-types|<name>"` — against a ruling that names ONE minting authority
  # (ADR-0016 ruling 5), and it retired into `hashIdentity`. A checker's identity is kind-tagged
  # like every other minted identity in the ecosystem: `"type:<digest>"`.
  #
  # ★ THE MINT ARRIVES INJECTED because gen-types is a LEAF and the authority used to live
  # downstream of it, in gen-schema — a cycle gen-types could never have closed. That is the whole
  # reason the authority became a dependency-free library of its own, and taking it as a parameter
  # is what a consumer upstream of the old home has to do.
  #
  # ★★ WHAT ENTERS THE PREIMAGE IS THE CONSTRUCTION — the constructor and its inert argument
  # value — AND NEVER THE NAME. A name is a RENDERING of a type, and a rendering is lossy: four
  # constructor families took content the name does not determine, and all four collided under
  # `typeEq` on the tree before this landing. Measured, one run, with `listOf<int>` vs
  # `listOf<str>` as the live control returning FALSE: `refined int positive` == `refined int
  # tcpPort` · `strict ["a"]` == `strict ["b"]` (every strict type is named "strict") · `enum
  # "colour" ["red"]` == `enum "colour" ["blue"]` · `struct "cfg" {a=int;}` == `struct "cfg"
  # {a=str;}` — all TRUE. That is Milner 1978 §3.3's failure exactly: semantically distinct values
  # admitted under one type, which is the direction a type discipline exists to exclude.
  #
  # ★ AND IT TRAVELLED, which is why the repair belongs here rather than in the four families.
  # Every combinator builds its name from its members' NAMES — `listOf<${t.name}>` — so one
  # colliding member collided the whole tree above it, and a fix scoped to the four constructors
  # would have left `listOf<cfg>` merging two different `cfg`s. A component that is a checker now
  # enters as its IDENTITY, so a composite is structural exactly as deep as its components are.
  #
  # ★ `ctor` AND `args` ARE BOTH REQUIRED AND NEITHER IS DEFAULTED. A defaulted argument value is
  # a silent name-mint at the one place the content is load-bearing — the defect above wearing a
  # new spelling. `ctor` is not redundant beside `args`: `strict [ "a" ]` and a hypothetical
  # `enum "strict" [ "a" ]` agree on every other component, and the constructor tag is what
  # separates them.
  #
  # ★★ THE REGIME IS DECIDED BY THE MINT, never by a second predicate kept in step by hand. The
  # encoder is total — it either encodes every node or refuses BY NAME — so handing it `args` and
  # reading its answer IS the classification. That is what routes a `struct` carrying a caller
  # `verify` lambda, a `refined` over caller predicates, and an `enum` over a path to the sealed
  # regime for the encoder's own stated reason, with no list of sealed cases here to fall out of
  # date. `tryEval` contains it because every refusal in the mint is a `throw` rather than a
  # builtin's own abort — which is the property gen-identity's encoder was built to have.
  mkChecker =
    ctor: args: name: verify:
    let
      mint =
        identity.hashIdentity "type"
          [
            "ctor"
            "args"
          ]
          (
            l:
            {
              inherit ctor args;
            }
            .${l}
          );
      attempt = tryEval mint;
    in
    {
      inherit name verify;
      check =
        v: v2:
        let
          e = verify v;
        in
        if e == null then v2 else throw e;
      __name = baseName name;

      # ★ `__mint` IS A TAGGED SUM AND IT IS TOTAL — every checker carries it, and a reader
      # dispatches on the TAG rather than branching on the field's presence. The relation in
      # `lib/default.nix` reads this and never `__id`.
      #
      # The sealed arm carries the constructor and points at the accessor rather than restating the
      # reason: `__id` re-runs the same mint UNCAUGHT, so a reader that wants the cause gets the
      # refusal that actually fired instead of a paraphrase kept in step by hand.
      #
      # ★ WHOSE REFUSAL THAT IS DIFFERS BY FAMILY, AND TWO OF THE THREE IS NOT ALL THREE. `refined`
      # and a `struct` carrying a caller `verify` reach the encoder with a lambda in `args`, so what
      # fires is gen-identity's own — "a lambda in an identity position". `typedef`/`typedef'` is the
      # excluded case and is excluded DELIBERATELY: it passes a throwing `args` of its own, because
      # the mint sees an argument value and cannot see the NAME of the type being declared, and
      # naming it is what makes the refusal actionable. That one message is this file's to keep true.
      __mint =
        if attempt.success then
          { minted = attempt.value; }
        else
          {
            unmintable = {
              inherit ctor;
              reason = "the mint refuses this construction's arguments; demand `__id` for its named refusal";
            };
          };

      # `__id` is the ACCESSOR a consumer reads when it DEMANDS an identity — it returns the
      # minted value, and on a value with no mintable identity it IS the named refusal. It is
      # LAZY, so a consumer that never demands one never hashes; and it is deliberately NOT what
      # the equality relation reads, because demanding an identity of a sealed value is a refusal
      # while DECIDING about one is not.
      __id = mint;
    };

  # A component that is itself a checker enters the preimage as its IDENTITY. A component with no
  # mintable identity refuses the composite BY NAME rather than through a missing attribute, so
  # what a reader sees is a refusal it can act on and not an evaluator message about an attrset.
  #
  # ★ ENTERING AS AN IDENTITY RATHER THAN AS A VALUE IS WHAT KEEPS TYPE NESTING OFF THE ENCODER'S
  # BOUNDS. An identity is a fixed 69 characters whatever it stands for, so a composite's preimage
  # is flat in the depth of the type it describes: measured, a 300-deep `listOf` chain mints and
  # separates from a 299-deep one, well past gen-identity's depth bound of 512 levels. The bound is
  # still real and still reachable — the control in the same run is a 600-deep list handed to `enum`
  # as a MEMBER, which is caller data, takes the full walk, and refuses.
  idOf =
    t: t.__mint.minted or (throw "identity: component type '${t.name}' has no mintable identity");

  # The substrate's own nullary vocabulary. `prim` is a REGISTRY of one argument — the primitive's
  # name — and it is total precisely because this library owns the predicate that name is bound to,
  # which is what the public `typedef` below cannot say of a caller's.
  prim = name: pred: mkChecker "prim" name name (v: if pred v then null else typeError name v);
  prim' = name: verify: mkChecker "prim" name name verify;

  self = fix (checkers: {
    # ── custom-type constructors ──

    # Declare a type from an option<str> verifier (null on success, message on error).
    #
    # ★ A CALLER-DECLARED TYPE IS SEALED, and that is ADR-0034's sealed limb rather than an
    # omission here. The verifier is a caller-supplied lambda; Nix exposes no eliminator for a
    # closure — no builtin reads a captured environment or a body — so no preimage over one can be
    # TOTAL, and an identity minted over a partial preimage merges behaviourally distinct
    # checkers. Minting over the NAME instead is the rejected remedy: it is a name-only identity at
    # a site that mints, and two callers declaring "port" over different predicates would share it.
    #
    # ★ WHAT WOULD HAVE TO CHANGE, named as the burden asymmetry requires: a caller whose predicate
    # is a FIRST-ORDER TERM the substrate interprets — a constructor plus an inert argument, built
    # through `mkChecker` — mints. That is the migration ADR-0034 requires and `refined` is the
    # ecosystem's first case of. Until then `typeEq` DECIDES about such a type by comparing the
    # reified record, which is finer than the name relation and never coarser.
    typedef' =
      name: verify:
      mkChecker "typedef"
        (throw "identity: type '${name}' is declared from a caller-supplied verifier, which is a lambda and has no total preimage")
        name
        verify;

    # Declare a type from a bool predicate; the standard type-mismatch message is
    # synthesized on failure. Sealed for the same reason as `typedef'`.
    typedef = name: pred: checkers.typedef' name (v: if pred v then null else typeError name v);

    # ── primitives (builtins.is* wrappers) ──
    # These take `prim` rather than the public `typedef`: their predicates are this library's, so
    # the name is a coordinate in a closed vocabulary and the preimage over it is total.
    string = prim "string" isString;
    str = checkers.string;
    int = prim "int" isInt;
    bool = prim "bool" isBool;
    float = prim "float" isFloat;
    number = prim "number" (v: isInt v || isFloat v);
    path = prim "path" isPath;
    pathLike = prim "pathLike" (v: isPath v || isDerivation v || isString v);
    attrs = prim "attrs" isAttrs;
    list = prim "list" isList;
    function = prim "function" isFunction;
    derivation = prim "derivation" isDerivation;
    null = prim "null" isNull;
    any = prim' "any" (_: null);
    never = prim "never" (_: false);

    # ── polymorphic combinators ──

    # option<t>: null, or a t.
    option =
      t:
      let
        name = "option<${t.name}>";
      in
      mkChecker "option" (idOf t) name (
        v: if v == null then null else addContext "in ${name}" (t.verify v)
      );

    # listOf<t>: a list whose every element is a t.
    listOf =
      t:
      let
        name = "listOf<${t.name}>";
      in
      mkChecker "listOf" (idOf t) name (
        v: if !isList v then typeError name v else addContext "in ${name} element" (firstError t.verify v)
      );

    # attrsOf<t>: an attrset whose every value is a t.
    attrsOf =
      t:
      let
        name = "attrsOf<${t.name}>";
      in
      mkChecker "attrsOf" (idOf t) name (
        v:
        if !isAttrs v then
          typeError name v
        else
          addContext "in ${name} value" (firstError t.verify (attrValues v))
      );

    # union<a,b,…>: a value satisfying at least one member (short-circuits).
    # Members enter the preimage IN ORDER: `union [ a b ]` and `union [ b a ]` accept the same
    # values but report a different name on failure, and finer is the safe direction here.
    union =
      types:
      assert isList types;
      let
        name = "union<${concatStringsSep "," (map (t: t.name) types)}>";
        funcs = map (t: t.verify) types;
      in
      mkChecker "union" (map idOf types) name (
        v: if any (f: f v == null) funcs then null else typeError name v
      );

    # intersection<a,b,…>: a value satisfying every member.
    intersection =
      types:
      assert isList types;
      let
        name = "intersection<${concatStringsSep "," (map (t: t.name) types)}>";
        funcs = map (t: t.verify) types;
      in
      mkChecker "intersection" (map idOf types) name (v: addContext "in ${name}" (firstFailing funcs v));

    # enum<name>: membership in a fixed set of literals.
    # The name is an ARGUMENT here rather than a rendering — it reaches the failure message — so it
    # enters the preimage beside the members instead of standing in for them.
    #
    # ★ MEMBERS ENTER IN ORDER AND WITH MULTIPLICITY, AND — UNLIKE `union` AND `strict` — WITH NO
    # OBSERVABLE THAT DISTINGUISHES THEM. That exclusion is the whole of the difference: `union`
    # reports its members in order in its own name, and `strict` renders its declared keys in order
    # in its blame string, so for those two a reordering genuinely is a different type. `enum "e"
    # [ "a" "b" ]` and `enum "e" [ "b" "a" ]` agree on the name, on the accept relation and on the
    # blame string — every observable the record carries — and still mint apart; so do `[ "a" "a" ]`
    # and `[ "a" ]`. Finer is the safe direction for a decision predicate, so this is DECLARED here
    # rather than repaired: `elems` IS this constructor's argument value and `[ "a" "b" ]` is not
    # `[ "b" "a" ]` under Nix `==`, so sorting or deduplicating would move the `==`-biconditional off
    # the argument value and would owe an argument of its own.
    enum =
      name: elems:
      assert isList elems;
      mkChecker "enum" { inherit name elems; } name (
        v: if elem v elems then null else "${toPretty v} is not a member of enum '${name}'"
      );

    # tuple<a,b,…>: a list of exactly the members, positionally typed.
    tuple =
      members:
      assert isList members;
      let
        name = "tuple<${concatStringsSep ", " (map (t: t.name) members)}>";
        len = length members;
        funcs = map (t: t.verify) members;
        walk =
          v: i:
          if i == len then
            null
          else
            let
              e = (elemAt funcs i) (elemAt v i);
            in
            if e != null then "in element ${toString i}: ${e}" else walk v (i + 1);
      in
      mkChecker "tuple" (map idOf members) name (
        v:
        if !isList v then
          typeError name v
        else if length v != len then
          "expected tuple of length ${toString len} but value ${toPretty v} has length ${toString (length v)}"
        else
          addContext "in ${name}" (walk v 0)
      );

    # optionalAttr<t>: a t, but flagged so struct treats the key as omittable.
    optionalAttr =
      t:
      let
        name = "optionalAttr<${t.name}>";
      in
      mkChecker "optionalAttr" (idOf t) name (v: addContext "in ${name}" (t.verify v));

    # struct<name>{ members }: a record. A freshly constructed struct starts from
    # the policy set total = true, unknown = true, verify = null.
    #
    # .override delta: a delta over the policy set the RECEIVER was built with.
    # A field the delta names is replaced; a field it leaves unmentioned is
    # retained. The result carries .override again, bound to the new set, so the
    # handle composes at any depth rather than restarting from the set above.
    #   total   — every member key must be present (optionalAttr members exempt)
    #   unknown — false rejects keys not declared as members (closed world)
    #   verify  — extra whole-record invariant (value -> null | err)
    #
    # Allocation frugality: member verifiers are precomputed once at construction
    # (name lookup + context baked in). The only intermediate attrset a verify can
    # allocate is the `removeAttrs` for the unknown-key check, and that is built
    # solely when unknown = false — the default happy path allocates nothing.
    struct =
      name: members:
      assert isAttrs members;
      let
        memberNames = attrNames members;
        ctx = "in struct '${name}'";
        build =
          {
            total ? true,
            unknown ? true,
            verify ? null,
          }:
          assert isBool total;
          assert isBool unknown;
          assert verify != null -> isFunction verify;
          let
            memberFuncs = map (
              attr:
              let
                mt = members.${attr};
                mctx = "in member '${attr}'";
                isOpt = mt.__name == "optionalAttr";
              in
              v:
              if v ? ${attr} then
                addContext mctx (mt.verify v.${attr})
              else if total && !isOpt then
                "missing member '${attr}'"
              else
                null
            ) memberNames;
            unknownFunc =
              v:
              let
                extra = attrNames (removeAttrs v memberNames);
              in
              if extra == [ ] then
                null
              else
                "keys [${joinKeys extra}] are unrecognized, expected keys are [${joinKeys memberNames}]";
            funcs = memberFuncs ++ optional (!unknown) unknownFunc ++ optional (verify != null) verify;
            verify' = v: if !isAttrs v then typeError name v else addContext ctx (firstFailing funcs v);
          in
          # ★ THE POLICY SET IS DISTINGUISHING CONTENT, not decoration: `total` and `unknown` change
          # which values the struct admits, so `.override` yields a DIFFERENT type and must yield a
          # different identity. They are booleans and enter the mint.
          #
          # ★★ `verify` IS WHERE THE PER-COMPONENT READING PAYS. It is a caller-supplied lambda, so
          # a struct carrying one is SEALED — and a struct without one is MINTED, over its members'
          # identities and its policy. The limb is per COMPONENT rather than per constructor, which
          # is what stops one struct's extra invariant from dragging every struct onto the
          # comparison limb. Nothing here tests for it: `verify = null` encodes and a lambda is
          # refused by the encoder, so the two arms fall out of the mint's own totality.
          mkChecker "struct" {
            inherit
              name
              total
              unknown
              verify
              ;
            members = mapAttrs (_: idOf) members;
          } name verify'
          // {
            override = delta: build ({ inherit total unknown verify; } // delta);
          };
      in
      build { };
  });
in
# The checker set is the library's public surface; `mkChecker` and `idOf` are the identity core
# the two fold-in files build on, and they are exported HERE rather than onto the set itself so
# that reaching them stays a `lib/`-internal privilege. A fold-in constructor needs the same
# by-construction identity every constructor above has — that is the whole point of there being
# one producer — but a CALLER stating a construction is the migration ADR-0034 leaves open, and
# publishing the door before the vocabulary is picked would decide it by accretion.
{
  checkers = self;
  inherit mkChecker idOf;
}
