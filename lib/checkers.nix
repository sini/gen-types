# gen-types — pure structural type CHECKERS.
#
# The checking half of a pure Nix module system: a value either satisfies a type
# (verify => null) or it does not (verify => an error string). This is contract
# checking in the sense of § Findler & Felleisen 2002 — a type is a boundary that
# blames the value on mismatch — restricted to a first-order, allocation-frugal
# core so it stays a single eval pass on the happy path.
#
# Every checker is a record { name; verify; check; __name; __nameWithin; __mint; __id; __payload; }:
#   name    — full structural name, e.g. "listOf<int>", within `renderBudget` bytes
#   verify  — value -> null | errString   (null = ok)
#   check   — v: v2: throws verify's error on failure, returns v2 on success
#   __name  — base name with polymorphic metadata stripped ("listOf")
#   __nameWithin — budget -> the name rendered within that many bytes; what a combinator
#             reads of a member instead of its `name` (see `renderNode`)
#   __mint — the identity REGIME as a tagged sum, minted over the CONSTRUCTION rather
#             than over the name: { minted = "type:<digest>"; } where the constructor's
#             arguments are inert, { unmintable = { ctor; reason; }; } where one of them
#             is a caller-supplied lambda. This is what the equality relation reads.
#   __id    — the accessor for a consumer that DEMANDS an identity: the minted value, or
#             the mint's own named refusal. Lazy, and never what the relation reads.
#   __payload — the construction the mint hashed, READ-ONLY and NON-IDENTITY-BEARING, as a total
#             tagged sum: { minted = { ctor; args; }; } where `__mint` is minted,
#             { unmintable = { ctor; }; } where it is not. Read it through `payloadOf`, which
#             certifies it against the digest (see `mkComposite`).
#   __okAt  — on a COMPOSITE only: the step-indexed guard over its members that bounds type
#             nesting for the mint (see `identityGuard`). A leaf carries none.
#   __sealed — the map from each SEALED component's path to its comparison subject, `{ }` where
#             every component is minted or inert: the part of the type its mark is blind to, and
#             what `typeEq` compares beside the mark (see `mkIdentity`).
#
# NO nixpkgs.lib here (purity invariant, see ci/tests/types-purity.nix): builtins
# plus the handful of gen-prelude utilities the substrate already vendors.
{
  prelude,
  identity,
  algebra,
}:
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
  # ★ A COMPOSITE NAME IS RENDERED WITHIN A BYTE BUDGET HANDED DOWN IN PREORDER, because Nix `let`
  # is recursive and a type can hold itself (`let r = union [ int (listOf r) ]; in r`). Its name
  # then denotes a regular infinite tree, and a name built by interpolating the members' `name`
  # thunks needs its own value: an uncatchable black hole on every refusal, so the type could
  # accept but never refuse. Here a combinator's name is `renderNode` applied to `nameBudget`, and
  # a member is rendered through its own renderer (`__nameWithin`) and never through its `name`.
  #
  # ★ TERMINATION: every member call is handed at most `inner = b - |open| - |close|`, and every
  # combinator's `open` is non-empty, so the budget is a natural number that strictly decreases at
  # each call. That holds for every name a gen-types combinator produces. A hand-built member that
  # builds its OWN name from the cycle (`{ name = "wrap<${r.name}>"; … }`) is a diverging name
  # producer outside this library, and it diverges here as it did before.
  #
  # ★ THE CEILING: a renderer handed b returns at most max(b, |…|) bytes. A node reserves its
  # brackets, and before a member with siblings after it, a separator and a `…`; once the budget is
  # spent the remaining members collapse into one `…`. The name is lossy past the budget, which
  # ADR-0034 admits: the derived name answers shape guards and is never hashed and never a key.
  #
  # ★ WHAT STAYS BYTE-IDENTICAL: a member is rendered whole whenever its full name fits the room it
  # is handed, and each nesting level spends at most the 3 B of that reservation, so a name of at
  # most 256 - 3d bytes (d its combinator nesting depth; 253 B when flat) renders exactly as the
  # unbounded interpolation did. Past that a fitting name can elide where a trailing member is
  # shorter than `…`: `union [ enum <247 B> (enum "e") ]` is `union<…,e>`. A member's name is read
  # from its construction-time renderer, so a record renamed by `//` keeps its old name as a
  # member, as its `__name` and `__mint` already do.
  nameBudget = renderBudget;
  ell = "…";
  leafWithin = n: b: if stringLength n <= b then n else ell;
  withinOf =
    ctor: t: b:
    if isAttrs t && isFunction (t.__nameWithin or null) then
      t.__nameWithin b
    else
      leafWithin (memberName ctor t) b;
  renderNode =
    ctor: open: sep: close: members: b:
    let
      inner = b - stringLength open - stringLength close;
      go =
        ms: left:
        if ms == [ ] then
          [ ]
        else
          let
            more = builtins.tail ms != [ ];
            room = left - (if more then stringLength sep + stringLength ell else 0);
            s = withinOf ctor (head ms) room;
          in
          # elide only a member that does not fit: one shorter than `…` fits a room smaller than it
          if stringLength s > room then
            [ ell ]
          else
            [ s ] ++ go (builtins.tail ms) (left - stringLength s - (if more then stringLength sep else 0));
    in
    if inner < stringLength ell then
      ell
    else
      "${open}${concatStringsSep sep (go members inner)}${close}";
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
  mkChecker = ctor: args: mkComposite ctor [ ] (_: args);

  # ★★ THE TYPE-NESTING AXIS HAS ITS OWN BOUND, because the flat preimage (`tagOf` below) takes type
  # nesting off the encoder's. Each `hashIdentity` call is bounded and total; the recursion runs
  # BETWEEN calls, through each member's memoised `__mint`, so a self-referential type
  # (`let r = union [ int (listOf r) ]; in r`) re-enters its own thunk — a blackhole `tryEval` does
  # not catch — and an acyclic chain about 950 deep overflows the stack. ADR-0034 puts both outside
  # the mint ("every self-referential value … The budget's refusal point is CHOSEN"), so such a type
  # takes the COMPARED regime: `__mint` is tagged `unmintable`, `typeEq` decides over the record, and
  # demanding `__id` is the named refusal below. Bounds rather than detection, as in gen-identity's
  # own header: Nix has no observation that two visited nodes are one, so a cycle and an over-deep
  # type are one refusal.
  #
  # ★ THE GUARD IS STEP-INDEXED (the k-th approximant of well-foundedness, Appel & McAllester 2001).
  # A composite's cell at index k holds iff k > 0 and every member's cell at k - 1 holds. Each read
  # is at a strictly smaller index, so no thunk is re-entered on a cycle — it bottoms out at index 0
  # and refuses — and each (node, k) cell is memoised, so the cost is linear in the type GRAPH and
  # never in its expansion: a DAG whose expansion is 2^128 still mints. A memoised height field
  # blackholes on the same cycle, and an unmemoised walk pays the expansion; those are the two
  # alternatives this rejects.
  #
  # ★ THE CELLS ARE A STREAM INDEXED DOWNWARD FROM THE BOUND, so only the cells a demand reaches are
  # allocated: a node at depth d below the demanded root allocates d + 1, and a shallow type one to
  # three. A leaf carries no stream at all; `top` stands in for it, and that absence is what leaves
  # a leaf's key set untouched for gen-merge.
  #
  # ★ THE BOUND IS A CONSTANT, NOT A PARAMETER, against gen-graph's "every cap is a maxDepth
  # PARAMETER" precedent (den-hoag-6ag6, den-hoag-82ib): a regime must be a function of the type
  # alone, and a caller-supplied depth would let two consumers disagree on whether one type mints.
  # The margin is what buys caller context. 128 levels mint in about 1,400 frames against the
  # evaluator's 10,000, and a refusal costs about 650; gen-identity's own `identityDepth` is a
  # constant with a margin argument too. A type between 129 and about 900 deep therefore moves from
  # MINTED to COMPARED, and at gen-merge an identical redeclaration of such a type is refused by name
  # rather than merged.
  typeIdentityDepth = 128;
  depthRefusal = throw "identity: a type nests deeper than the type-identity depth bound (${toString typeIdentityDepth} levels); a self-referential type has no identity";
  #
  # ★ THE STREAM ENDS AT INDEX 0 (`next = null`), which no read reaches because the cell at 0 holds
  # without reading its members. An unending stream would make `deepSeq` of every composite type
  # diverge, since it forces through `__okAt`. A leaf's stand-in is one shared chain of the same
  # length, memoised here.
  topFrom = k: {
    ok = true;
    next = if k == 0 then null else topFrom (k - 1);
  };
  top = topFrom typeIdentityDepth;
  cellOf = m: if isAttrs m && m ? __okAt then m.__okAt else top;
  step = k: cells: {
    ok = k > 0 && all (c: c.next.ok) cells;
    next = if k == 0 then null else step (k - 1) (map (c: c.next) cells);
  };
  # The guard over a construction's members, for every producer that mints over a member's `__mint`:
  # `okAt` is what the producer carries as `__okAt`, `ok` gates its mint, and `refusal` is its
  # `__id` when `ok` fails. A producer that mints over members and carries no `__okAt` reopens the
  # blackhole for any cycle through it.
  identityGuard =
    members:
    let
      okAt = step typeIdentityDepth (map cellOf members);
    in
    {
      inherit okAt;
      ok = members == [ ] || okAt.ok;
      refusal = depthRefusal;
    };

  # The comparison SUBJECT for the sealed arm: the reified record MINUS its two accessors,
  # `__id` and `__okAt`, and minus nothing else — preceded by its own closure fields (below).
  #
  # ★ `__id` IS AN ACCESSOR, NOT DISTINGUISHING CONTENT, and in the sealed regime that
  # accessor IS the named refusal. Comparing the record without excluding it forces the
  # refusal inside a decision the refusal exists to permit, and the decision detonates.
  # Measured on a sealed checker carrying a throwing `__id`: self-comparison of the
  # unexcluded record ABORTS, and a distinct pair survives only because a lambda-valued
  # attribute happens to be compared first and short-circuits — an ordering accident,
  # not a property. Excluding the accessor removes both.
  #
  # ★ The alternative — making `__id` ABSENT on a sealed checker — is rejected: it would
  # delete the named refusal a consumer that DEMANDS an identity must receive, trading a
  # detonation for a silent missing attribute.
  #
  # `removeAttrs` preserves the evaluator's cell fast path (measured: a record compared
  # with itself through it stays equal, two separately-built records stay unequal, and
  # on a record with no `__id` it is a byte-for-byte no-op), so this excludes the
  # accessor without emptying the relation.
  #
  # ★ WHY EXCLUDING `__id` IS SUFFICIENT AND NOT ARBITRARY. It is the only OTHER
  # refusal-valued accessor a compared value can carry, because `__mint.minted` is
  # shielded by the tagged sum's own shape: the minted and sealed arms live under
  # DIFFERENT KEY NAMES, and Nix `==` decides on the name set before forcing any value.
  # Measured, with its control: a throwing payload under a differently-named key is
  # never reached, while the SAME name on both sides DOES force — so the short-circuit
  # is the name check, not throws being ignored. Two sealed values carry inert payloads
  # under one name, so nothing forces there either. The one path that does force a mint
  # is a minted-against-minted comparison, and that arm never reaches here: it compares
  # digests, which is a genuine DEMAND for an identity, where a catchable named refusal
  # is the correct outcome rather than a hazard.
  #
  # ★ `__okAt` IS EXCLUDED BESIDE IT, on a different ground: it is total (a cyclic type's stream
  # bottoms out at index 0), so nothing detonates, but it is an accessor rather than distinguishing
  # content, and comparing it would force up to `typeIdentityDepth + 1` cells of each side.
  #
  # ★ CLOSURES FIRST (`den-hoag-6xj95`; ADR-0034's compared limb). The subject is a two-element
  # list: `K`, the record's declared closure fields that are present as functions, then the whole
  # record. List `==` decides index 0 before it touches index 1, and `==` on two functions answers
  # without entering either closure, so a pair whose `K` differs is `false` before any of the
  # record's own attributes is compared. The order matters for records carrying a BACK-EDGE: a
  # nixpkgs record's `functor.type` is a late-bound lookup into its own lib, so across two lib
  # instances (`lib.extend`, or two nixpkgs inputs) attrset `==`, which walks attributes in
  # symbol-interning order, can reach that edge before the first difference and recurse until the
  # evaluator aborts with an UNCATCHABLE stack overflow — on host Nix, Determinate Nix and Lix
  # alike, depending on what text was parsed first. Every nixpkgs `mkOptionType` call builds its
  # own `typeMerge` closure, and so does gen-merge's, so distinct constructions differ in `K`. `K`
  # is a sub-attrset of the record holding the same slots: this is still one `==` over a subject
  # containing the whole reified value, never a component-wise replacement of it.
  #
  # THE VALUE, SCOPED. Where the bare record `==` returns a boolean and every listed field present
  # is total at WHNF, this subject returns the same boolean. Outside that domain the value moves,
  # both ways: a listed field that throws when forced turns a bare `false` into that throw (the
  # `isFunction` filter forces it), and a self-referential nixpkgs type compared across two
  # instances (`let x = either str (listOf x)`) turns `infinite recursion` into `false`.
  #
  # ★ ENUMERATED EXCEPTION TO TOTALITY (ADR-0025 item 1: "enumerated and argued, never silent").
  # The comparison can still abort, uncatchably and depending on interning order, where `K` is
  # EQUAL and the record's `==` then reaches a back-edge before a difference:
  #   1. A GRAFT: every closure slot shared, another attribute holding distinct cross-instance
  #      data — `t.port // { foo = t.port; }` against `t.port // { foo = u.port; }`, or a
  #      `functor` grafted from each instance. Sharing every closure slot means sharing the
  #      construction, and a plain `//`-derivation shares its back-edges too and terminates, so
  #      only a hand graft of cross-instance data reaches this. Foreign COMPOSITES reach it too
  #      since `identityOf` stopped minting them: `let x = listOf str; in x // { foo = t.port; }`
  #      against `x // { foo = u.port; }` aborts depending on interning order, where the mint
  #      used to answer.
  #   2. A record carrying NONE of the listed fields as a function: `K` is `{}` on both sides, the
  #      prefix is vacuously equal and the bare `==` decides alone. A producer whose closure fields
  #      carry other names lands here until this list names them.
  # Closing either needs an evaluator-observable value identity — a visited set — which pure Nix
  # does not expose. Same-instance comparisons take the slot shortcut and are unaffected.
  #
  # ★ A DECLARED SUBJECT IS THE SUBJECT: a registered construction (gen-algebra `mkIntensional`)
  # names its comparison subject, its registry coordinate, constructor and inert arguments, and that
  # is answered instead of the record, whose `fn` is a lambda rebuilt per construction.
  comparisonSubject =
    v:
    if algebra.hasDeclaredSubject v then
      v.__mint.unmintable.subject
    else
      let
        s = removeAttrs v [
          "__id"
          "__okAt"
        ];
        # The closure fields declared by every record producer: nixpkgs' and gen-merge's
        # `mkOptionType`, and this library's `mkChecker`/`mkComposite`.
        sealedKeys = filter (n: s ? ${n} && isFunction s.${n}) [
          "check"
          "merge"
          "typeMerge"
          "getSubOptions"
          "substSubModules"
          "verify"
          "__nameWithin"
        ];
      in
      [
        (builtins.intersectAttrs (prelude.genAttrs sealedKeys (_: null)) s)
        s
      ];

  # ★★ THE PER-COMPONENT IDENTITY OF A TYPE (ADR-0034's per-component clause; den-hoag-6orb8), the
  # half every constructor shares and the one a producer outside this library builds through. A
  # type's MARK is minted over its constructor and its argument value, in which each member enters
  # by a TAG: a minted member by its digest, and a SEALED member (one carrying no minted `__mint`, or
  # whose `check` a wrapper rewrote — the check-witness protocol below) by gen-algebra's
  # `sealedMarker`. A constructor's own sealed arguments (a caller's predicate, a struct's `verify`)
  # are tagged the same way by the constructor. So a composite STAYS MINTED whatever its components'
  # regimes, and one sealed component no longer drags it onto the compared regime.
  #
  # Beside the mark the type carries `__sealed`, gen-algebra `componentsPreimage`'s map from each
  # sealed component's path to its comparison subject: a sealed member as this library's
  # `comparisonSubject` of it (closures first), a lambda in its own slot, a registered construction
  # as `{ compared = <its declared subject>; }`, and a minted member that itself seals something as
  # its own `__sealed` (PROPAGATION). The mark is blind to all of it, so it is NEVER a key on its own:
  # `typeEq` decides over both (`sealedCollisionEq`), `__id` refuses a demand while `__sealed` is
  # non-empty, and `payloadOf` refuses to read a payload that is not a total preimage.
  #
  # ★ THE PREIMAGE IS THE ONE IT WAS FOR A TYPE WHOSE COMPONENTS ARE ALL MINTED OR INERT: a member's
  # tag is its digest, as it was, so every such digest is unchanged and only types that used to be
  # unmintable gain a mark.
  #
  # ★ `args` IS BUILT FROM `members`, never beside them: a member's tag reaches the preimage only
  # through `mkArgs tags`, where `tags` reads the same members the guard reads. Two lists kept in
  # step by hand reopen the blackhole silently for a constructor that passes one and not the other.
  # `members` is a list, or an attrset whose `tags` are keyed alike. `sealed` is a list of the
  # constructor's own sealed arguments, `{ path = [ <segment> ]; value; }`, each of which `mkArgs`
  # places as `sealedMarker`.
  #
  # Returns the identity fields: `__mint`, `__id`, `__payload`, `__sealed`, and `__okAt` on a
  # composite. `name` words the refusals.
  isSealedMember =
    t: !(isAttrs t) || rewritesCheck t || !(t ? __mint && isAttrs t.__mint && t.__mint ? minted);
  tagOf = t: if isSealedMember t then algebra.sealedMarker else t.__mint.minted;
  mkIdentity =
    ctor: members: mkArgs: sealed: name:
    let
      memberList = if isList members then members else attrValues members;
      keyed =
        if isList members then
          builtins.genList (i: {
            k = toString i;
            t = elemAt members i;
          }) (length members)
        else
          map (k: {
            inherit k;
            t = members.${k};
          }) (attrNames members);
      tags = if isList members then map tagOf members else mapAttrs (_: tagOf) members;
      args = mkArgs tags;
      guard = identityGuard memberList;
      pre = algebra.componentsPreimage identity.hashIdentity (
        map (
          m:
          if isSealedMember m.t then
            {
              path = [
                "members"
                m.k
              ];
              value = if isAttrs m.t then comparisonSubject m.t else m.t;
              sealed = true;
            }
          else
            {
              path = [
                "members"
                m.k
              ];
              value = m.t;
            }
        ) keyed
        ++ map (c: c // { sealed = true; }) sealed
      );
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
      attempt = if guard.ok then tryEval mint else { success = false; };
    in
    {
      # ★ `__mint` IS A TAGGED SUM AND IT IS TOTAL — every checker carries it, and a reader
      # dispatches on the TAG rather than branching on the field's presence. The relation in
      # `lib/default.nix` reads this and never `__id`.
      #
      # The sealed arm carries the constructor and points at the accessor rather than restating the
      # reason: `__id` re-runs the same mint UNCAUGHT, so a reader that wants the cause gets the
      # refusal that actually fired instead of a paraphrase kept in step by hand. It is reached by a
      # type past the type-identity bound, and by arguments the encoder refuses outside the
      # constructor's declared sealed ones (an `enum` over a path).
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
      # minted value, and on a value with no exact identity it IS the named refusal. It is LAZY, so
      # a consumer that never demands one never hashes; and it is deliberately NOT what the
      # equality relation reads, because demanding an identity of a sealed value is a refusal while
      # DECIDING about one is not. A mark beside a non-empty `__sealed` is not an exact identity.
      __id =
        if !guard.ok then
          guard.refusal
        else if pre.sealed != { } then
          throw "identity: type '${name}' has sealed component(s) ${
            concatStringsSep ", " (map (k: "'${k}'") (attrNames pre.sealed))
          } (a caller-supplied lambda, a registered construction, or a type with no minted identity), which its mark is blind to: it is decided by `typeEq` and has no identity to demand"
        else
          mint;

      # ★ `__payload` IS THE MINT'S OWN PREIMAGE, RETAINED READ-ONLY, AND IT BEARS NO IDENTITY
      # (owner ruling on den-hoag-parametric-merge-unlock-6wb87, 2026-08-27; design of record
      # den-ag-design `reports/den-hoag-nqhoa-readsurface-spec-v0.md`). Identity stays with
      # `__mint.minted`, and `__id` answers every demand for one; a reader treating this field as
      # identity re-opens the name-vs-structure confusion the construction mint closed. It is
      # never a key and enters no mint.
      #
      # ★ TOTAL AND TAGGED, like `__mint`, and for the same reason: the key is always present and
      # its value is lazy, so reading the record's key set forces no mint (a regime-dependent key
      # would, and on a self-referential type that is `identityGuard`'s blackhole). It is decided by
      # the same `attempt` as `__mint`, so the minted arm holds only what the encoder certified
      # inert: no lambda, no path, no derivation. A sealed component appears in it as
      # `sealedMarker`, and `payloadOf` refuses a record whose `__sealed` is non-empty.
      #
      # ★ ON THE COMPARED REGIME THIS FIELD JOINS `comparisonSubject`'s record (lib/default.nix),
      # which can only make `==` finer, never turn false into true. Its two arms sit under different
      # key names, the shielding `__mint` uses, so a sealed-against-minted pair decides on the name
      # set before either value is forced. A `//`-derived record can carry a `minted` payload beside
      # a different `__mint`; that payload was certified inert at its own mint, so nothing detonates,
      # and `payloadOf` refuses it because it is not the preimage of the digest the record carries.
      #
      # ★ `payloadOf` INVOKES THE ONE MINTING AUTHORITY AND ADDS NONE: it re-runs `hashIdentity`
      # over this preimage and compares the result with `__mint.minted`, and nothing it computes
      # escapes that comparison. The cost is one `hashIdentity` per read, bounded by gen-identity's
      # preimage bounds; a caller folding N declarations pays 2(N−1) re-mints over a growing
      # argument.
      __payload =
        if attempt.success then
          {
            minted = {
              inherit ctor args;
            };
          }
        else
          {
            unmintable = {
              inherit ctor;
            };
          };
      __sealed = pre.sealed;
    }
    // (if memberList == [ ] then { } else { __okAt = guard.okAt; });

  mkComposite =
    ctor: members: mkArgs:
    mkCompositeSealed ctor members mkArgs [ ];
  mkCompositeSealed =
    ctor: members: mkArgs: sealed: name0: verify:
    let
      # a combinator hands a RENDERER (budget -> string), a leaf or a nominal type its name
      name = if isFunction name0 then name0 nameBudget else name0;
      within = if isFunction name0 then name0 else leafWithin name0;
    in
    {
      inherit name verify;
      __nameWithin = within;
      check =
        v: v2:
        let
          e = verify v;
        in
        if e == null then v2 else throw e;
      __name = baseName name;
    }
    // mkIdentity ctor members mkArgs sealed name;

  # ★ A MEMBER ENTERS THE PREIMAGE AS ITS IDENTITY, AND THAT IS WHAT KEEPS TYPE NESTING OFF THE
  # ENCODER'S BOUNDS. An identity is a fixed 69 characters whatever it stands for, so a composite's
  # preimage is flat in the depth of the type it describes, and type nesting is bounded instead by
  # `typeIdentityDepth` above: a 128-deep `listOf` chain mints and separates from a 127-deep one,
  # and a 129-deep one is unmintable. gen-identity's own depth bound is still real and still
  # reachable — a 600-deep list handed to `enum` as a MEMBER is caller data, takes the full walk,
  # and refuses. A member with no minted identity enters as `sealedMarker` (`tagOf`, above).

  # ★ A NAME THAT IS NOT A STRING REFUSES BY NAME WHERE IT IS READ. Every combinator renders a
  # member that carries no `__nameWithin` from its `name`, and four constructors (`typedef`, `typedef'`, `enum`,
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

  # ── THE CHECK-WITNESS PROTOCOL (den-hoag-ydro3). This library owns it: a producer builds the
  # pair with `witnessedCheck`, a reader asks `rewritesCheck`. A producer on a per-construction
  # cost budget may take the one record from `witnessRecord` and publish it under both fields
  # itself; `witnessedCheck`'s output is then the layout it is held to (owner ruling on
  # den-hoag-ydro3, arm (c)).
  #
  # A member whose published `check` a wrapper rewrote. A producer publishes its `check` beside
  # `_checkWitness`, which holds the same value, so a nixpkgs `addCheck` or `// { check = ...; }`
  # over it is the one record whose `check` no longer holds the witness. Total over records whose
  # `check` reaches WHNF: a record with no witness (this library's own checkers) answers `false`.
  rewritesCheck = t: t ? _checkWitness && t ? check && t.check != t._checkWitness;

  # The nixpkgs-protocol `check` a producer publishes over a domain `fn`, with its witness: one
  # functor record `{ __functor; _fn; }` bound once and published twice, so `rewritesCheck`
  # compares one set of bindings by the pointers of its slots and allocates nothing per test.
  checkApplies = self: self._fn;
  # The one record alone: what `witnessedCheck` publishes under both fields.
  witnessRecord = fn: {
    __functor = checkApplies;
    _fn = fn;
  };
  witnessedCheck =
    fn:
    let
      check = witnessRecord fn;
    in
    {
      inherit check;
      _checkWitness = check;
    };

  # A member read as a VERIFIER: its `verify`, and, where a wrapper rewrote its `check`, that check
  # too, since the record then states its domain twice and the rewrite is a refinement of it.
  # Decided once per member, when the combinator binds it, never per value.
  verifierOf =
    ctor: t:
    if rewritesCheck t then
      v:
      let
        e = t.verify v;
      in
      if e != null then
        e
      else if t.check v then
        null
      else
        "value ${toPretty v} is outside the `check' a wrapper stated over '${memberName ctor t}' (`addCheck', or `// { check = ...; }'), which ${ctor} carries"
    else
      t.verify;

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
      map (verifierOf ctor) ts
    else
      throw "gen-types: ${ctor}: member '${nm (head bad)}' is not a checker (it carries no `verify`); ${ctor} composes value predicates, and a merge strategy is not one";

  # The substrate's own nullary vocabulary. `prim` is a REGISTRY of one argument — the primitive's
  # name — and it is total precisely because this library owns the predicate that name is bound to,
  # which is what the public `typedef` below cannot say of a caller's.
  prim = name: pred: mkChecker "prim" name name (v: if pred v then null else typeError name v);
  prim' = name: verify: mkChecker "prim" name name verify;

  # A caller's predicate is a FUNCTION (a lambda or a functor) or a registered construction, which
  # is a functor too; anything else is refused by name, naming the door and the accepted forms.
  predicateDoor =
    door: name: what: f:
    if prelude.isFunction f then
      null
    else
      throw "gen-types: ${door}: the ${what} of type '${name}' must be a function or a registered construction (gen-algebra `mkIntensional`), but it is of type '${typeOf f}'";
  # A constructor's own sealed argument for `mkIdentity`. A registered construction is handed over
  # whole (its declared subject is what is compared); anything else keeps the slot it was passed in.
  sealedArg = path: value: { inherit path value; };

  self = fix (checkers: {
    # ── custom-type constructors ──

    # Declare a type from an option<str> verifier (null on success, message on error).
    #
    # ★ A CALLER-DECLARED PREDICATE IS A SEALED COMPONENT, and that is ADR-0034's per-component
    # reading. The type MINTS over its constructor and its name, and the predicate enters as
    # `sealedMarker` with its subject in `__sealed`: a caller lambda in its own slot, so one binding
    # declared twice decides `true` and two separately written lambdas are refused by name (Nix
    # exposes no eliminator for a closure, so no preimage over one is total); a REGISTERED
    # construction (gen-algebra `mkIntensional`) as its declared subject, so two constructions of one
    # term decide `true` and a different argument or revision `false`. Minting over the predicate is
    # the rejected remedy: no total preimage exists for a lambda, and a registered digest is a
    # decision predicate, never a key.
    #
    # ★ THE DOOR TAKES A FUNCTION OR A REGISTERED CONSTRUCTION AND NOTHING ELSE, refused by name and
    # catchably when the type is built: anything else would abort uncatchably at its first `verify`.
    typedef' =
      name0: verify:
      let
        name = callerName "typedef" name0;
      in
      seq name (
        seq (predicateDoor "typedef'" name "verifier" verify) (
          mkCompositeSealed "typedef'" [ ] (_: {
            inherit name;
            verify = algebra.sealedMarker;
          }) [ (sealedArg [ "verify" ] verify) ] name verify
        )
      );

    # Declare a type from a bool predicate; the standard type-mismatch message is
    # synthesized on failure. The caller's predicate, not the synthesized verifier, is the sealed
    # component, so one predicate declared twice is one type.
    typedef =
      name0: pred:
      let
        name = callerName "typedef" name0;
      in
      seq name (
        seq (predicateDoor "typedef" name "predicate" pred) (
          mkCompositeSealed "typedef" [ ] (_: {
            inherit name;
            pred = algebra.sealedMarker;
          }) [ (sealedArg [ "pred" ] pred) ] name (v: if pred v then null else typeError name v)
        )
      );

    # ── primitives (builtins.is* wrappers; `function`, `path`, `pathLike`: the nixpkgs predicates) ──
    # These take `prim` rather than the public `typedef`: their predicates are this library's, so
    # the name is a coordinate in a closed vocabulary and the preimage over it is total.
    string = prim "string" isString;
    str = checkers.string;
    int = prim "int" isInt;
    bool = prim "bool" isBool;
    float = prim "float" isFloat;
    number = prim "number" (v: isInt v || isFloat v);
    # nixpkgs' `types.path` (`pathWith { absolute = true; }`) and `pathWith { }`, over nixpkgs'
    # `lib.isStringLike` read by name from gen-prelude: string-like, and for `path` absolute, a
    # derivation counting as absolute without coercing it. String context is irrelevant.
    path = prim "path" (
      v: prelude.isStringLike v && (isDerivation v || substring 0 1 (toString v) == "/")
    );
    pathLike = prim "pathLike" prelude.isStringLike;
    attrs = prim "attrs" isAttrs;
    list = prim "list" isList;
    # nixpkgs' `lib.isFunction`, read by name from gen-prelude: a functor whose `__functor` returns a
    # function is a function, as `setFunctionArgs`, `witnessedCheck` and `prelude.door` build.
    function = prim "function" prelude.isFunction;
    derivation = prim "derivation" isDerivation;
    null = prim "null" isNull;
    any = prim' "any" (_: null);
    never = prim "never" (_: false);

    # ── polymorphic combinators ──

    # option<t>: null, or a t.
    option =
      t:
      let
        render = renderNode "option" "option<" "" ">" [ t ];
        name = render nameBudget;
        f = head (verifiersOf "option" [ t ]);
      in
      mkComposite "option" [ t ] head render (
        v: seq f (if v == null then null else addContext "in ${name}" (f v))
      );

    # listOf<t>: a list whose every element is a t.
    listOf =
      t:
      let
        render = renderNode "listOf" "listOf<" "" ">" [ t ];
        name = render nameBudget;
        f = head (verifiersOf "listOf" [ t ]);
      in
      mkComposite "listOf" [ t ] head render (
        v: seq f (if !isList v then typeError name v else addContext "in ${name} element" (firstError f v))
      );

    # attrsOf<t>: an attrset whose every value is a t.
    attrsOf =
      t:
      let
        render = renderNode "attrsOf" "attrsOf<" "" ">" [ t ];
        name = render nameBudget;
        f = head (verifiersOf "attrsOf" [ t ]);
      in
      mkComposite "attrsOf" [ t ] head render (
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
        render = renderNode "union" "union<" "," ">" types;
        name = render nameBudget;
        funcs = verifiersOf "union" types;
      in
      mkComposite "union" types (ids: ids) render (
        v: seq funcs (if any (f: f v == null) funcs then null else typeError name v)
      );

    # intersection<a,b,…>: a value satisfying every member.
    intersection =
      types:
      assert isList types;
      let
        render = renderNode "intersection" "intersection<" "," ">" types;
        name = render nameBudget;
        funcs = verifiersOf "intersection" types;
      in
      mkComposite "intersection" types (ids: ids) render (
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
        render = renderNode "tuple" "tuple<" ", " ">" members;
        name = render nameBudget;
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
      mkComposite "tuple" members (ids: ids) render (
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
        render = renderNode "optionalAttr" "optionalAttr<" "" ">" [ t ];
        name = render nameBudget;
        f = head (verifiersOf "optionalAttr" [ t ]);
      in
      mkComposite "optionalAttr" [ t ] head render (v: seq f (addContext "in ${name}" (f v)));

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
                mv = verifierOf "struct '${name}'" mt;
                mctx = "in member '${attr}'";
                isOpt = mt.__name == "optionalAttr";
              in
              v:
              if v ? ${attr} then
                addContext mctx (mv v.${attr})
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
          # it is a SEALED component: the struct mints over its members' identities, its policy and
          # `sealedMarker` in its place, and carries the lambda in `__sealed`. The limb is per
          # COMPONENT rather than per constructor, which is what stops one struct's extra invariant
          # from dragging every struct onto the comparison limb.
          mkCompositeSealed "struct" members (ids: {
            inherit name total unknown;
            verify = if verify == null then null else algebra.sealedMarker;
            members = ids;
          }) (optional (verify != null) (sealedArg [ "verify" ] verify)) name verify'
          // {
            override = delta: build ({ inherit total unknown verify; } // delta);
          };
      in
      seq name (build { });
  });
in
# The checker set is the library's public surface; `mkChecker` and `mkIdentity` are the identity core
# the two fold-in files build on, and they are exported HERE rather than onto the set itself so
# that reaching them stays a `lib/`-internal privilege. A fold-in constructor needs the same
# by-construction identity every constructor above has — that is the whole point of there being
# one producer — but a CALLER stating a construction is the migration ADR-0034 leaves open, and
# publishing the door before the vocabulary is picked would decide it by accretion.
{
  checkers = self;
  inherit
    mkChecker
    mkComposite
    mkCompositeSealed
    mkIdentity
    identityGuard
    comparisonSubject
    verifiersOf
    rewritesCheck
    witnessedCheck
    witnessRecord
    renderNode
    typeIdentityDepth
    ;
}
