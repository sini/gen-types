# gen-types — pure structural type CHECKERS.
#
# The checking half of a pure Nix module system: a value either satisfies a type
# (verify => null) or it does not (verify => an error string). This is contract
# checking in the sense of § Findler & Felleisen 2002 — a type is a boundary that
# blames the value on mismatch — restricted to a first-order, allocation-frugal
# core so it stays a single eval pass on the happy path.
#
# Every checker is a record { name; verify; check; __name; __id; }:
#   name    — full structural name, e.g. "listOf<int>"
#   verify  — value -> null | errString   (null = ok)
#   check   — v: v2: throws verify's error on failure, returns v2 on success
#   __name  — base name with polymorphic metadata stripped ("listOf")
#   __id    — name-derived intensional identity (Palmer-style, name-only ceiling):
#             two types are intensionally equal iff their names are, hashed like
#             gen-schema's id_hash (sha256 over the identifying content).
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
    optional
    ;
  inherit (builtins)
    isFloat
    isInt
    isPath
    removeAttrs
    split
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
  # (ADR-0016 ruling 5), and it retires here into `hashIdentity`. A checker's identity is now
  # kind-tagged like every other minted identity in the ecosystem: `"type:<digest>"`.
  #
  # ★ THE MINT ARRIVES INJECTED because gen-types is a LEAF and the authority used to live
  # downstream of it, in gen-schema — a cycle gen-types could never have closed. That is the whole
  # reason the authority became a dependency-free library of its own, and taking it as a parameter
  # is what a consumer upstream of the old home has to do.
  #
  # ★ WHAT ENTERS THE PREIMAGE IS THE NAME, AND ONLY THE NAME. A checker's `check` is a bare
  # lambda, and no preimage over a lambda can be TOTAL — so a mint over the whole checker record
  # would merge behaviourally distinct checkers, which for a relation that MINTS is the unsafe
  # direction with no safe alternative. The name is what `mkId` hashed too; what changed is the
  # authority and the tag, not the distinguishing content.
  mintType = name: identity.hashIdentity "type" [ "name" ] (_: name);

  self = fix (checkers: {
    # ── custom-type constructors ──

    # Declare a type from an option<str> verifier (null on success, message on error).
    typedef' = name: verify: {
      inherit name verify;
      check =
        v: v2:
        let
          e = verify v;
        in
        if e == null then v2 else throw e;
      __name = baseName name;

      # ★ `__mint` IS A TAGGED SUM AND IT IS TOTAL — every checker carries it, and a reader
      # dispatches on the TAG rather than branching on the field's presence. A checker minted over
      # its name is `minted`; nothing here is sealed, because a name is always mint-admissible.
      # The relation in `lib/default.nix` reads this and never `__id`.
      __mint.minted = mintType name;

      # `__id` survives as the ACCESSOR a consumer reads when it DEMANDS an identity — it returns
      # the minted value, and on a value with no mintable identity it would throw by name. It is
      # LAZY, so a consumer that never demands one never hashes; and it is deliberately NOT what
      # the equality relation reads, because demanding an identity of a sealed value is a refusal
      # while DECIDING about one is not.
      __id = mintType name;
    };

    # Declare a type from a bool predicate; the standard type-mismatch message is
    # synthesized on failure.
    typedef = name: pred: checkers.typedef' name (v: if pred v then null else typeError name v);

    # ── primitives (builtins.is* wrappers) ──
    string = checkers.typedef "string" isString;
    str = checkers.string;
    int = checkers.typedef "int" isInt;
    bool = checkers.typedef "bool" isBool;
    float = checkers.typedef "float" isFloat;
    number = checkers.typedef "number" (v: isInt v || isFloat v);
    path = checkers.typedef "path" isPath;
    pathLike = checkers.typedef "pathLike" (v: isPath v || isDerivation v || isString v);
    attrs = checkers.typedef "attrs" isAttrs;
    list = checkers.typedef "list" isList;
    function = checkers.typedef "function" isFunction;
    derivation = checkers.typedef "derivation" isDerivation;
    null = checkers.typedef "null" isNull;
    any = checkers.typedef' "any" (_: null);
    never = checkers.typedef "never" (_: false);

    # ── polymorphic combinators ──

    # option<t>: null, or a t.
    option =
      t:
      let
        name = "option<${t.name}>";
      in
      checkers.typedef' name (v: if v == null then null else addContext "in ${name}" (t.verify v));

    # listOf<t>: a list whose every element is a t.
    listOf =
      t:
      let
        name = "listOf<${t.name}>";
      in
      checkers.typedef' name (
        v: if !isList v then typeError name v else addContext "in ${name} element" (firstError t.verify v)
      );

    # attrsOf<t>: an attrset whose every value is a t.
    attrsOf =
      t:
      let
        name = "attrsOf<${t.name}>";
      in
      checkers.typedef' name (
        v:
        if !isAttrs v then
          typeError name v
        else
          addContext "in ${name} value" (firstError t.verify (attrValues v))
      );

    # union<a,b,…>: a value satisfying at least one member (short-circuits).
    union =
      types:
      assert isList types;
      let
        name = "union<${concatStringsSep "," (map (t: t.name) types)}>";
        funcs = map (t: t.verify) types;
      in
      checkers.typedef' name (v: if any (f: f v == null) funcs then null else typeError name v);

    # intersection<a,b,…>: a value satisfying every member.
    intersection =
      types:
      assert isList types;
      let
        name = "intersection<${concatStringsSep "," (map (t: t.name) types)}>";
        funcs = map (t: t.verify) types;
      in
      checkers.typedef' name (v: addContext "in ${name}" (firstFailing funcs v));

    # enum<name>: membership in a fixed set of literals.
    enum =
      name: elems:
      assert isList elems;
      checkers.typedef' name (
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
      checkers.typedef' name (
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
      checkers.typedef' name (v: addContext "in ${name}" (t.verify v));

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
          checkers.typedef' name verify'
          // {
            override = delta: build ({ inherit total unknown verify; } // delta);
          };
      in
      build { };
  });
in
self
