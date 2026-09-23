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
    filter
    isFloat
    isInt
    isPath
    removeAttrs
    seq
    split
    stringLength
    substring
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

  # A SHALLOW, TOTAL value renderer: it reads the value it is handed, which every door has
  # already forced to WHNF, and NEVER a member of it. A container shows its attribute names or
  # its length, which the evaluator answers without forcing a member thunk; a member's value is
  # `…`. So nothing a member raises when forced (a throw, an evaluator error, a cycle, a depth)
  # can reach it, and no refusal rendered through it aborts or is replaced. There is no
  # derivation arm: recognising a derivation reads `type`, which is a member.
  #
  # ★ `renderBudget` bounds the rendered value in bytes: a string or path is cut at it, and a
  # set's `name = …;` entries fill it in `attrNames` order and count the rest. Ceiling:
  # renderBudget + 34 bytes, for every value except a top-level float, whose `toString` is
  # bounded by its representation and not by the budget (1.5e300 renders 308 B). The bound is
  # on THIS value slot only: struct's closed-world refusal and `strict` list unknown key names
  # through `joinKeys`, which this renderer does not reach.
  renderBudget = 256;
  cut = s: if stringLength s > renderBudget then "${substring 0 renderBudget s}…" else s;
  toPretty =
    v:
    if isString v then
      ''"${cut v}"''
    else if isInt v || isFloat v then
      toString v
    else if isBool v then
      (if v then "true" else "false")
    else if isNull v then
      "null"
    else if isPath v then
      cut (toString v)
    else if isFunction v then
      "«lambda»"
    else if isList v then
      let
        n = length v;
      in
      if n == 0 then "[  ]" else "[ … (${toString n} element${if n == 1 then "" else "s"}) ]"
    else if isAttrs v then
      let
        names = attrNames v;
        n = length names;
        fill =
          i: used:
          let
            e = "${elemAt names i} = …;";
            u = used + stringLength e + 1;
          in
          if i == n || u > renderBudget then [ ] else [ e ] ++ fill (i + 1) u;
        shown = fill 0 0;
        rest = n - length shown;
      in
      "{ ${concatStringsSep " " (shown ++ optional (rest > 0) "… (${toString rest} more)")} }"
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
    t:
    t.__mint.minted
      or (throw "identity: component type '${memberName "identity" t}' has no mintable identity");

  # ★ A NAME THAT IS NOT A STRING REFUSES BY NAME WHERE IT IS READ. Every combinator interpolates
  # its members' `name` into its own, and four constructors (`typedef`, `typedef'`, `enum`,
  # `struct`) interpolate a caller's; interpolating a non-string aborts uncatchably. A member's
  # name is read lazily, because forcing it at formation diverges on a self-referential type; a
  # caller's is forced when the constructor is applied, so the bad type never forms.
  memberName =
    ctor: t:
    let
      n = if isAttrs t then t.name or null else null;
    in
    if isString n then
      n
    else
      throw "gen-types: ${ctor}: a member's `name` must be a string, but it is ${
        if n != null then
          "of type '${typeOf n}'"
        else if isAttrs t then
          "absent"
        else
          "absent (the member is of type '${typeOf t}')"
      }";
  callerName =
    ctor: name:
    if isString name then
      name
    else
      throw "gen-types: ${ctor}: the type's name must be a string, but it is of type '${typeOf name}'";

  # A combinator's members, read as VERIFIERS. A member that is not a checker (no `verify`: a
  # merge strategy, which carries `admits` instead, or a non-attrset) refuses the combinator BY
  # NAME, catchably, where a bare `t.verify` would abort with an evaluator message.
  #
  # ★ THE CHECK RUNS AT USE, NOT AT FORMATION. Each combinator binds this list once in its own
  # `let` and `seq`s it on entry to `verify`: forcing the list to WHNF runs the whole filter, so
  # the refusal cannot depend on the value or on member order, and the check is shared across
  # every call. Forcing it when the combinator is APPLIED instead diverges on a self-referential
  # type (`let r = union [ int (listOf r) ]; in r`), which answers at use.
  #
  # ★ IT REACHES ONLY THE COMBINATOR DIRECTLY HOLDING THE MEMBER. A non-checker nested one level
  # further in is read only when the outer combinator dispatches to it, so these still answer
  # `null` for an ill-formed type: `listOf (union [ str m ])` given `[ ]`, `option (union [ str m ])`
  # given `null`, and a struct key declared `optionalAttr m` when the key is absent. Refusing those
  # would take a hereditary check, which is the formation-time force above.
  verifiersOf =
    ctor: ts:
    let
      bad = filter (t: !(isAttrs t && t ? verify)) ts;
      nm =
        t:
        if !(isAttrs t) then
          "<a ${typeOf t}>"
        else if isString (t.name or null) then
          t.name
        else
          "<unnamed>";
    in
    if bad == [ ] then
      map (t: t.verify) ts
    else
      throw "gen-types: ${ctor}: member '${nm (head bad)}' is not a checker (it carries no `verify`); ${ctor} composes value predicates, and a merge strategy is not one";

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
      name0: verify:
      let
        name = callerName "typedef" name0;
      in
      seq name (
        mkChecker "typedef"
          (throw "identity: type '${name}' is declared from a caller-supplied verifier, which is a lambda and has no total preimage")
          name
          verify
      );

    # Declare a type from a bool predicate; the standard type-mismatch message is
    # synthesized on failure. Sealed for the same reason as `typedef'`.
    typedef =
      name0: pred:
      let
        name = callerName "typedef" name0;
      in
      checkers.typedef' name (v: if pred v then null else typeError name v);

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
        name = "option<${memberName "option" t}>";
        f = head (verifiersOf "option" [ t ]);
      in
      mkChecker "option" (idOf t) name (
        v: seq f (if v == null then null else addContext "in ${name}" (f v))
      );

    # listOf<t>: a list whose every element is a t.
    listOf =
      t:
      let
        name = "listOf<${memberName "listOf" t}>";
        f = head (verifiersOf "listOf" [ t ]);
      in
      mkChecker "listOf" (idOf t) name (
        v: seq f (if !isList v then typeError name v else addContext "in ${name} element" (firstError f v))
      );

    # attrsOf<t>: an attrset whose every value is a t.
    attrsOf =
      t:
      let
        name = "attrsOf<${memberName "attrsOf" t}>";
        f = head (verifiersOf "attrsOf" [ t ]);
      in
      mkChecker "attrsOf" (idOf t) name (
        v:
        seq f (
          if !isAttrs v then typeError name v else addContext "in ${name} value" (firstError f (attrValues v))
        )
      );

    # union<a,b,…>: a value satisfying at least one member (short-circuits).
    # Members enter the preimage IN ORDER: `union [ a b ]` and `union [ b a ]` accept the same
    # values but report a different name on failure, and finer is the safe direction here.
    #
    # ★ union DECIDES BY `f v == null`, so it builds each refusing member's message on its way to
    # the member that accepts. With the shallow `toPretty` that message cannot abort on the value.
    # The known limit, and it is LOUD: a failing member whose message ITSELF throws (a caller's
    # `refined` message, a `typedef'` verifier) raises that error from union's verify, which can
    # refuse a value a later member accepts. It never answers a false `null`.
    union =
      types:
      assert isList types;
      let
        name = "union<${concatStringsSep "," (map (memberName "union") types)}>";
        funcs = verifiersOf "union" types;
      in
      mkChecker "union" (map idOf types) name (
        v: seq funcs (if any (f: f v == null) funcs then null else typeError name v)
      );

    # intersection<a,b,…>: a value satisfying every member.
    intersection =
      types:
      assert isList types;
      let
        name = "intersection<${concatStringsSep "," (map (memberName "intersection") types)}>";
        funcs = verifiersOf "intersection" types;
      in
      mkChecker "intersection" (map idOf types) name (
        v: seq funcs (addContext "in ${name}" (firstFailing funcs v))
      );

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
      name0: elems:
      assert isList elems;
      let
        name = callerName "enum" name0;
      in
      seq name (
        mkChecker "enum" { inherit name elems; } name (
          v: if elem v elems then null else "${toPretty v} is not a member of enum '${name}'"
        )
      );

    # tuple<a,b,…>: a list of exactly the members, positionally typed.
    tuple =
      members:
      assert isList members;
      let
        name = "tuple<${concatStringsSep ", " (map (memberName "tuple") members)}>";
        len = length members;
        funcs = verifiersOf "tuple" members;
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
        seq funcs (
          if !isList v then
            typeError name v
          else if length v != len then
            "expected tuple of length ${toString len} but value ${toPretty v} has length ${toString (length v)}"
          else
            addContext "in ${name}" (walk v 0)
        )
      );

    # optionalAttr<t>: a t, but flagged so struct treats the key as omittable.
    optionalAttr =
      t:
      let
        name = "optionalAttr<${memberName "optionalAttr" t}>";
        f = head (verifiersOf "optionalAttr" [ t ]);
      in
      mkChecker "optionalAttr" (idOf t) name (v: seq f (addContext "in ${name}" (f v)));

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
      name0: members:
      assert isAttrs members;
      let
        name = callerName "struct" name0;
        memberNames = attrNames members;
        ctx = "in struct '${name}'";
        # forced on entry to `verify`, before any member's `__name` or `verify` is read
        memberCheck = verifiersOf "struct '${name}'" (attrValues members);
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
            verify' =
              v: seq memberCheck (if !isAttrs v then typeError name v else addContext ctx (firstFailing funcs v));
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
      seq name (build { });
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
  inherit mkChecker idOf verifiersOf;
}
