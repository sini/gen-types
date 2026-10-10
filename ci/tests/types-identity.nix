# gen-types: checker identity — __name, idOf, and conservative equality (typeEq /
# conservativeEq), which dispatches on the checker's identity REGIME.
{ genTypes, lib, ... }:
let
  t = genTypes;
  ft = lib.types;

  # Fixtures for the two regimes a producer stamps. The producer has since landed and
  # every SHIPPED checker now carries a `__mint`, so these hand-built records are what
  # pin the RELATION's arms independently of what the constructors currently emit — a
  # digest pair the constructors cannot be made to produce, and a sealed record whose
  # accessor detonates on contact.
  #
  # ★ A CHECKER'S FIELDS ARE TOTAL DATA. A consumer that DEMANDS an identity calls `idOf`, a
  # projection over `__mint` and `__sealed`, so no fixture carries a field that refuses when
  # forced: a comparison IS a consumer, and it reads every field (den-hoag-6orb8 A1).
  mkMinted = n: digest: {
    name = n;
    __name = n;
    verify = _: null;
    check = v: _: v;
    __mint.minted = digest;
    __sealed = { };
  };
  mkUnmintable = n: {
    name = n;
    __name = n;
    verify = _: null;
    check = v: _: v;
    __mint.unmintable = {
      reason = "the refinement predicate is a caller-supplied lambda";
      ctor = n;
    };
  };
  # CONTROL fixture: a minted checker carrying a field that would detonate if read. The minted
  # arm decides on digests and must never reach the record.
  mkMintedPoisoned =
    n: digest:
    (mkMinted n digest)
    // {
      zz = throw "the minted arm must not force the record";
    };
  mintedChecker = mkMinted;
  unmintableChecker = mkUnmintable "refined<str>";
  evaluates = e: (builtins.tryEval e).success;

  # A record carrying no `__mint` at all — a foreign checker, or one built before the
  # producer landed. Nothing this library constructs can be one, so the UNMIGRATED arm
  # has no other subject and would otherwise be asserted about by nothing.
  unmigratedChecker = n: {
    name = n;
    __name = n;
    verify = _: null;
    check = v: _: v;
  };

  # The identity REGIME as a readable tag, so a cell states which arm a construction
  # lands on rather than asserting a digest nobody can read.
  regimeOf = c: if c.__mint ? minted then "minted" else "unmintable:${c.__mint.unmintable.ctor}";
  r = t.refinements;
in
{
  flake.tests.types-identity.test-basename-primitive = {
    expr = t.int.__name;
    expected = "int";
  };
  flake.tests.types-identity.test-basename-strips-poly = {
    expr = (t.checkedListOf t.int).__name;
    expected = "listOf";
  };
  flake.tests.types-identity.test-fullname-keeps-poly = {
    expr = (t.checkedListOf t.int).name;
    expected = "listOf<int>";
  };
  # ★ THE FORMAT MOVED WITH THE AUTHORITY, and the cell asserts the SHAPE rather than a length now.
  # `mkId` emitted a bare 64-character digest over `"gen-types|<name>"` — a SECOND hashing surface
  # against a ruling that names one. It retired into `hashIdentity`, so a checker's identity is
  # kind-tagged like every other minted identity in the ecosystem: `"type:" ++ 64 hex`, 69
  # characters. Asserting the tagged shape says what the format IS; asserting 69 would only say how
  # long it is, and would pass for any other five-character prefix.
  flake.tests.types-identity.test-id-is-kind-tagged-sha256 = {
    expr = {
      shape = builtins.match "type:[0-9a-f]{64}" (t.idOf t.int) != null;
      length = builtins.stringLength (t.idOf t.int);
    };
    expected = {
      shape = true;
      length = 69;
    };
  };
  flake.tests.types-identity.test-typeEq-same-structural-name = {
    # two independently-constructed listOf<int> are intensionally equal
    expr = t.typeEq (t.checkedListOf t.int) (t.checkedListOf t.int);
    expected = true;
  };
  flake.tests.types-identity.test-typeEq-different-names = {
    expr = t.typeEq t.int t.str;
    expected = false;
  };
  flake.tests.types-identity.test-typeEq-primitive-self = {
    expr = t.typeEq t.int t.int;
    expected = true;
  };
  flake.tests.types-identity.test-typeEq-nested-distinct = {
    expr = t.typeEq (t.checkedListOf t.int) (t.checkedListOf t.str);
    expected = false;
  };
  flake.tests.types-identity.test-conservativeEq-alias = {
    expr = t.conservativeEq t.bool t.bool;
    expected = true;
  };
  flake.tests.types-identity.test-str-alias-shares-identity = {
    # str is a definitional alias of string; both carry name "string"
    expr = t.typeEq t.str t.string;
    expected = true;
  };

  # ── the four colliding constructor families ─────────────────────────────────
  #
  # ★★★ THIS IS THE CELL THE DEFECT LIVED BEHIND. `__id` hashed the type NAME alone, and
  # a name is a lossy rendering of a type: `strict` names every instance "strict", `enum`
  # and `struct` take their name from the caller, and `refined<t>` says nothing about the
  # predicates. Measured on the tree before this landing, every arm below read TRUE —
  # semantically distinct types admitted as one, which is precisely the failure Milner
  # 1978 §3.3 holds a type discipline responsible for excluding.
  #
  # The two controls are what make the reading mean something, and they sit in the same
  # cell so they cannot be run separately from it: `listOf<int>` vs `listOf<str>` was
  # FALSE before and after — the relation could always separate where the name encoded
  # the structure — and the green twin says the relation still answers TRUE where it
  # should, so a fix that simply broke equality everywhere is not what this reports.
  flake.tests.types-identity.test-four-families-no-longer-collide = {
    expr = {
      refined = t.typeEq (t.refined t.int r.positive) (t.refined t.int r.tcpPort);
      strict = t.typeEq (t.strict [ "a" ]) (t.strict [ "b" ]);
      enum = t.typeEq (t.enum "colour" [ "red" ]) (t.enum "colour" [ "blue" ]);
      struct = t.typeEq (t.struct "cfg" { a = t.int; }) (t.struct "cfg" { a = t.str; });
      # The enum name is an ARGUMENT — it reaches the failure message — so two enums over
      # the same members under different names are distinct types.
      enumName = t.typeEq (t.enum "colour" [ "red" ]) (t.enum "size" [ "red" ]);
      # GREEN TWIN: same construction, separately built, still equal in every family that
      # mints. `refined` is absent here on purpose — it is sealed, and its twin is the
      # allocation-artefact cell below.
      twinStrict = t.typeEq (t.strict [ "a" ]) (t.strict [ "a" ]);
      twinEnum = t.typeEq (t.enum "colour" [ "red" ]) (t.enum "colour" [ "red" ]);
      twinStruct = t.typeEq (t.struct "cfg" { a = t.int; }) (t.struct "cfg" { a = t.int; });
      # CONTROL, unchanged by this landing in both directions.
      controlDistinct = t.typeEq (t.checkedListOf t.int) (t.checkedListOf t.str);
      controlSame = t.typeEq (t.checkedListOf t.int) (t.checkedListOf t.int);
    };
    expected = {
      refined = false;
      strict = false;
      enum = false;
      struct = false;
      enumName = false;
      twinStrict = true;
      twinEnum = true;
      twinStruct = true;
      controlDistinct = false;
      controlSame = true;
    };
  };

  # ★★ AND THE COLLISION TRAVELLED, which is why the repair is at the one record producer
  # and not in the four constructors. Every combinator builds its name from its members'
  # NAMES, so a colliding member collided the whole tree above it: measured before this
  # landing, `listOf` over two different `struct "cfg"` and `attrsOf` over two different
  # `enum "e"` both read TRUE. A member now enters its composite's preimage as its
  # IDENTITY, so a composite is structural exactly as deep as its members are.
  flake.tests.types-identity.test-collision-does-not-travel-through-combinators = {
    expr = {
      listOfStructs = t.typeEq (t.checkedListOf (t.struct "cfg" { a = t.int; })) (
        t.checkedListOf (t.struct "cfg" { a = t.str; })
      );
      attrsOfEnums = t.typeEq (t.checkedAttrsOf (t.enum "e" [ "a" ])) (
        t.checkedAttrsOf (t.enum "e" [ "b" ])
      );
      tupleOfStructs = t.typeEq (t.tuple [ (t.struct "cfg" { a = t.int; }) ]) (
        t.tuple [ (t.struct "cfg" { a = t.str; }) ]
      );
      # A composite over a member with a SEALED component stays MINTED (ADR-0034's
      # per-component clause): it mints over the member's mark and carries the member's
      # sealed subject under the member's path, so the mark never decides alone.
      composingASealedMember = regimeOf (t.checkedListOf (t.refined t.int r.positive));
      sealedTravels = builtins.attrNames (t.checkedListOf (t.refined t.int r.positive)).__sealed;

      # ★★ AND REFLEXIVITY OVER CONSTRUCTION HOLDS WHERE THE SEALED COMPONENT IS ONE BINDING.
      # Two `refined` constructions over the one stock refinement carry its `check` in its own
      # slot, so they decide `true`, and so does a composite over them. Two separately written
      # lambdas are still refused (`types-identity-sealed.nix`), and `controlEqualMembers` below
      # is the minted control.
      refinedSelf = t.typeEq (t.refined t.int r.positive) (t.refined t.int r.positive);
      listOfRefinedSelf = t.typeEq (t.checkedListOf (t.refined t.int r.positive)) (
        t.checkedListOf (t.refined t.int r.positive)
      );

      # CONTROL: composites over EQUAL members still compare equal, so this is a finer
      # relation and not a broken one.
      controlEqualMembers = t.typeEq (t.checkedListOf (t.struct "cfg" { a = t.int; })) (
        t.checkedListOf (t.struct "cfg" { a = t.int; })
      );
    };
    expected = {
      listOfStructs = false;
      attrsOfEnums = false;
      tupleOfStructs = false;
      composingASealedMember = "minted";
      sealedTravels = [ "members.0" ];
      refinedSelf = true;
      listOfRefinedSelf = true;
      controlEqualMembers = true;
    };
  };

  # The three regimes are decided BY CONSTRUCTOR at the declaration, never by inspecting a
  # value — and the decision is the MINT'S: `args` either encodes totally or the encoder
  # refuses it by name. So the sealed rows are sealed for a stated reason (a caller lambda
  # in the arguments) rather than by a list in the library that could drift.
  #
  # ★ The per-component reading pays out on every constructor: a caller lambda (a struct's
  # `verify`, a refinement's `check`, a `typedef`'s predicate) is a SEALED COMPONENT, so the type
  # still mints, over the rest, and carries the lambda in `__sealed`
  # (`test-sealed-constructions-refuse-when-an-identity-is-demanded` holds the demand's refusal).
  #
  # ★★ THIS CELL IS ALSO THE GUARD ON A MINT THAT STOPS WORKING, which is the one price of
  # letting the mint decide the regime: a `hashIdentity` that refused everything would
  # send every construction to the sealed arm, and `typeEq` would keep answering — finer,
  # so never unsound, but silently less able. Nothing else here would notice, because a
  # sealed answer is a legitimate answer. Pinning the regime PER CONSTRUCTOR is what makes
  # that visible: the minted rows flip to `unmintable:…` and this cell reddens.
  flake.tests.types-identity.test-identity-regime-is-decided-by-constructor = {
    expr = {
      prim = regimeOf t.int;
      listOf = regimeOf (t.checkedListOf t.int);
      enum = regimeOf (t.enum "colour" [ "red" ]);
      strict = regimeOf (t.strict [ "a" ]);
      struct = regimeOf (t.struct "cfg" { a = t.int; });
      structWithCallerVerify = regimeOf ((t.struct "cfg" { a = t.int; }).override { verify = _: null; });
      refined = regimeOf (t.refined t.int r.positive);
      callerTypedef = regimeOf (t.typedef "port" (v: v > 0));
    };
    expected = {
      prim = "minted";
      listOf = "minted";
      enum = "minted";
      strict = "minted";
      struct = "minted";
      structWithCallerVerify = "minted";
      refined = "minted";
      callerTypedef = "minted";
    };
  };

  # A sealed construction gets NO identity and a NAMED refusal when one is demanded through
  # `idOf`, a function, so the record itself stays total under `deepSeq`. These are the SHIPPED
  # constructors rather than fixtures, so the cell fails if a constructor quietly starts
  # minting over a partial preimage.
  flake.tests.types-identity.test-sealed-constructions-refuse-when-an-identity-is-demanded = {
    expr = {
      refined = evaluates (t.idOf (t.refined t.int r.positive));
      structWithCallerVerify = evaluates (t.idOf ((t.struct "s" { }).override { verify = _: null; }));
      callerTypedef = evaluates (t.idOf (t.typedef "port" (v: v > 0)));
      # CONTROL, same run: the same demand on a minted checker returns a kind-tagged
      # identity cleanly, so these refusals are the sealed regime and not a broken mint.
      mintedStillAnswers =
        builtins.match "type:[0-9a-f]{64}" (t.idOf (t.struct "cfg" { a = t.int; })) != null;
    };
    expected = {
      refined = false;
      structWithCallerVerify = false;
      callerTypedef = false;
      mintedStillAnswers = true;
    };
  };

  # The struct policy set changes which values the struct ADMITS, so `.override` yields a
  # different type and owes a different identity. Under a name-only identity it could not:
  # `.override` does not touch the name.
  flake.tests.types-identity.test-struct-policy-is-distinguishing-content = {
    expr = {
      total = t.typeEq (t.struct "s" { a = t.int; }) (
        (t.struct "s" { a = t.int; }).override { total = false; }
      );
      unknown = t.typeEq (t.struct "s" { a = t.int; }) (
        (t.struct "s" { a = t.int; }).override { unknown = false; }
      );
      # CONTROL: an override that restates the shipped policy is the same type.
      identityOverride = t.typeEq (t.struct "s" { a = t.int; }) (
        (t.struct "s" { a = t.int; }).override { total = true; }
      );
    };
    expected = {
      total = false;
      unknown = false;
      identityOverride = true;
    };
  };

  # The constructor TAG is load-bearing beside the arguments, and this is the pair that
  # says so: `option t` and `listOf t` both take one checker, so their argument values are
  # byte-identical and the name is not in the preimage. Only the tag separates them.
  #
  # ★ THIS CELL IS NOT ONE OF THE LANDING'S SEEDED REDS, stated so its green is not read as
  # evidence of one. It passed on the pre-fix tree too, where the differing NAMES carried
  # it. What it guards is the construction going forward, and it is armed against exactly
  # that: with the `ctor` label removed from the preimage this cell FAILS while the shipped
  # tree passes — measured in one run.
  flake.tests.types-identity.test-constructor-tag-separates-equal-arguments = {
    expr = t.typeEq (t.checkedOption t.int) (t.checkedListOf t.int);
    expected = false;
  };

  # ── conservative equality by identity REGIME ────────────────────────────────
  # The cells above run on SHIPPED constructors, every one of which is stamped, so they
  # exercise the minted and sealed arms. The cells below pin the relation's arms on
  # fixtures instead — the shapes a constructor cannot be made to emit.

  flake.tests.types-identity.test-minted-same-digest-eq = {
    expr = t.typeEq (mintedChecker "a" "type:dddd") (mintedChecker "b" "type:dddd");
    expected = true;
  };

  flake.tests.types-identity.test-minted-different-digest-neq = {
    # Same NAME, different digest: the digest decides and the name does not, which
    # is the whole point of moving the relation off `name`.
    expr = t.typeEq (mintedChecker "a" "type:dddd") (mintedChecker "a" "type:eeee");
    expected = false;
  };

  # A checker that declares it has no mintable identity must be DECIDED, never
  # detonate. `idOf` is the DEMAND, and refuses when there is no identity; a consumer that
  # decides dispatches on `__mint` instead, and compares a record none of whose fields refuses.
  flake.tests.types-identity.test-unmintable-self-eq = {
    expr = t.typeEq unmintableChecker unmintableChecker;
    expected = true;
  };

  # The refusal stays REACHABLE for a consumer that DEMANDS an identity, through `idOf`, and the
  # record carries no field that refuses: the retired `__id` accessor is absent from what the
  # shipped constructor builds (den-hoag-6orb8 A1; pre-release, no tombstone).
  flake.tests.types-identity.test-unmintable-id-still-refuses-by-name = {
    expr = {
      carriesNoAccessor = !((t.typedef "port" (v: v > 0)) ? __id);
      demandingItRefuses = !(evaluates (t.idOf unmintableChecker));
      # CONTROL: the same demand on a minted checker returns the identity cleanly.
      mintedDemandSucceeds = t.idOf (mkMinted "a" "type:dddd");
    };
    expected = {
      carriesNoAccessor = true;
      demandingItRefuses = true;
      mintedDemandSucceeds = "type:dddd";
    };
  };

  # CONTROL: the minted arm decides on digests and never reaches the record — proven
  # by poisoning a field. A run where this throws means the minted arm fell through.
  flake.tests.types-identity.test-minted-arm-never-forces-the-record = {
    expr = {
      equal = t.typeEq (mkMintedPoisoned "a" "type:dddd") (mkMintedPoisoned "b" "type:dddd");
      distinct = t.typeEq (mkMintedPoisoned "a" "type:dddd") (mkMintedPoisoned "a" "type:eeee");
    };
    expected = {
      equal = true;
      distinct = false;
    };
  };

  # CONTROL: the unmintable arm's precision is an allocation artefact — two
  # separately-built sealed checkers compare unequal. Finer is the safe direction
  # for a type-equality decision: the failure a type discipline exists to exclude
  # is answering TRUE wrongly.
  flake.tests.types-identity.test-unmintable-separately-built-neq = {
    expr = t.typeEq unmintableChecker (mkUnmintable "refined<str>");
    expected = false;
  };

  # There is no name arm: a record with neither `__mint` nor `nestedTypes` is compared over
  # the whole reified record, so two built apart are not equal by name alone. The fixture
  # keeps that population covered by a cell asserting the removal.
  flake.tests.types-identity.test-unmigrated-records-are-not-equal-by-name = {
    expr = {
      sameName = t.typeEq (unmigratedChecker "foo") (unmigratedChecker "foo");
      differentName = t.typeEq (unmigratedChecker "foo") (unmigratedChecker "bar");
      # CONTROL: a stamped checker on one side was never a name match either.
      mixedWithMinted = t.typeEq (unmigratedChecker "int") t.int;
    };
    expected = {
      sameName = false;
      differentName = false;
      mixedWithMinted = false;
    };
  };

  flake.tests.types-identity.test-conservativeEq-is-typeEq-on-every-regime = {
    expr = {
      unmigrated =
        t.conservativeEq (unmigratedChecker "foo") (unmigratedChecker "foo")
        == t.typeEq (unmigratedChecker "foo") (unmigratedChecker "foo");
      minted =
        t.conservativeEq (mintedChecker "a" "type:dddd") (mintedChecker "b" "type:dddd")
        == t.typeEq (mintedChecker "a" "type:dddd") (mintedChecker "b" "type:dddd");
      unmintable =
        t.conservativeEq unmintableChecker unmintableChecker
        == t.typeEq unmintableChecker unmintableChecker;
    };
    expected = {
      unmigrated = true;
      minted = true;
      unmintable = true;
    };
  };

  # ── foreign (nixpkgs) type identity — 2026-09-17 spec, gate conditions 1 & 2 ──
  #
  # `lib.types.*` is nixpkgs' own combinator family: genuine `mkOptionType` records carrying no
  # `__mint`, which is what makes `identityOf`'s `nestedTypes` branch live. RED before this
  # landing (re-derived fresh against the unmodified `typeEq`, same session): both `differentElem`
  # and the enum row below read `true`. GREEN is what these cells now pin.
  flake.tests.types-identity.test-foreign-listOf-discriminates-structurally = {
    expr = {
      differentElem = t.typeEq (ft.listOf ft.str) (ft.listOf ft.int);
      # POSITIVE CONTROL: not "always false" — one listOf<str> binding equals itself. Separately
      # built twins are compared as records and unequal (`den-hoag-hc755`); no cell pins that.
      sharedBinding =
        let
          x = ft.listOf ft.str;
        in
        t.typeEq x x;
    };
    expected = {
      differentElem = false;
      sharedBinding = true;
    };
  };

  # gen-native CONTROL, same run: the native path was never broken and stays unchanged.
  flake.tests.types-identity.test-foreign-listOf-gen-native-control = {
    expr = t.typeEq (t.checkedListOf t.str) (t.checkedListOf t.int);
    expected = false;
  };

  # Gate condition 2's shipped row: a BROKEN-family member (empty `nestedTypes`, distinguishing
  # content outside `.name`/`.nestedTypes`) as a refusal/discrimination control. Two
  # differently-valued enums must not mint identically — discriminate or refuse by name, either is
  # acceptable; silently minting the same identity is the defect this row exists to catch.
  flake.tests.types-identity.test-foreign-enum-does-not-silently-unify = {
    expr = t.typeEq (ft.enum [ "a" ]) (ft.enum [ "b" ]);
    expected = false;
  };

  # `pathWith`'s three callers (`path`, `pathInStore`, `externalPath`) all share the hardcoded name
  # `"path"` while differing in accept/reject behaviour, so any mint over the name reproduces the
  # defect. This pins the pair apart so a later name-keyed foreign mint cannot regress it silently.
  flake.tests.types-identity.test-foreign-path-family-not-falsely-unified = {
    expr = t.typeEq ft.path ft.pathInStore;
    expected = false;
  };

  # ★ den-hoag-6orb8 A1: A TYPE RECORD CARRIES NO `__id` FIELD, so `deepSeq` of every shipped
  # construction is total, the sealed ones included (each threw under `deepSeq` while the field was
  # the refusal). The demand moved to `idOf`, which answers exactly what the cached `__mint` holds.
  # Reds on a producer that carries the retired field again.
  flake.tests.types-identity.test-a-type-record-is-total-under-deepSeq =
    let
      shapes = {
        int = t.int;
        listOfInt = t.checkedListOf t.int;
        typedef = t.typedef "port" (v: v > 0);
        listOfTypedef = t.checkedListOf (t.typedef "port" (v: v > 0));
        refined = t.refined t.int r.positive;
        structOverride = (t.struct "s" { }).override { verify = _: null; };
        enum = t.enum "e" [ "a" ];
      };
    in
    {
      expr = {
        carriesNoId = builtins.all (v: !(v ? __id)) (builtins.attrValues shapes);
        deepForces = builtins.mapAttrs (_: v: (builtins.tryEval (builtins.deepSeq v true)).success) shapes;
        # the demand is a projection: it answers the cached mint itself
        idOfIsTheMint = t.idOf t.int == t.int.__mint.minted;
        sealedRefused = evaluates (t.idOf shapes.listOfTypedef);
      };
      expected = {
        carriesNoId = true;
        deepForces = {
          int = true;
          listOfInt = true;
          typedef = true;
          listOfTypedef = true;
          refined = true;
          structOverride = true;
          enum = true;
        };
        idOfIsTheMint = true;
        sealedRefused = false;
      };
    };

  # ★ "idOf NEVER RE-MINTS" (den-hoag-6orb8 A1): a record whose stored mint is not the digest of its
  # payload must answer the STORED string, since a re-mint answers the payload's digest instead. It has
  # no `__typeSelf`, so it is a non-copy and reaches the projection. Reds on any guarded re-mint.
  flake.tests.types-identity.test-idOf-answers-the-stored-mint-never-a-re-mint = {
    expr = t.idOf (
      removeAttrs t.int [ "__typeSelf" ] // { __mint.minted = "type:stored-not-the-payload-digest"; }
    );
    expected = "type:stored-not-the-payload-digest";
  };

  # The compared subject excludes `__okAt` and nothing else: a field named `__id` is ordinary content
  # now that no producer carries a refusal under it. Reds on a build that still strips it.
  flake.tests.types-identity.test-comparison-subject-keeps-every-field-but-okAt = {
    expr =
      let
        s = builtins.elemAt (t.comparisonSubject (t.checkedListOf t.int // { __id = "kept"; })) 1;
      in
      {
        id = s.__id or null;
        okAt = s ? __okAt;
      };
    expected = {
      id = "kept";
      okAt = false;
    };
  };
}
