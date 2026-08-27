# gen-types: checker identity — __name, __id, and conservative equality (typeEq /
# conservativeEq), which dispatches on the checker's identity REGIME.
{ genTypes, ... }:
let
  t = genTypes;

  # Fixtures for the two regimes a producer stamps. The producer has since landed and
  # every SHIPPED checker now carries a `__mint`, so these hand-built records are what
  # pin the RELATION's arms independently of what the constructors currently emit — a
  # digest pair the constructors cannot be made to produce, and a sealed record whose
  # accessor detonates on contact.
  #
  # ★ THESE ARE SITE-7 SHAPED, AND CARRYING `__id` IS THE POINT. The producer keeps
  # `__id` as the accessor a consumer reads when it DEMANDS an identity: it returns the
  # minted value, or it IS the named refusal. So a sealed checker carries a THROWING
  # `__id`, and the sealed arm must decide without forcing it — which is why
  # `conservativeEq` compares the record minus that one field.
  #
  # Fixtures that omitted `__id` could not have caught this, and the reason is worth
  # recording: the design's own note that `__id` "stays lazy, so it is invisible to
  # consumers that do not read it" is what made a comparison look safe — a comparison IS
  # a consumer, and it reads every field. A spec-trail append recording that is OWED;
  # the spec is not edited from here.
  mkMinted = n: digest: {
    name = n;
    __name = n;
    verify = _: null;
    check = v: _: v;
    __mint.minted = digest;
    __id = digest;
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
    __id = throw "identity: '${n}' has no mintable identity";
  };
  # CONTROL fixture: a minted checker whose accessor would detonate if read. The minted
  # arm decides on digests and must never reach it.
  mkMintedPoisonedId =
    n: digest:
    (mkMinted n digest)
    // {
      __id = throw "identity: the minted arm must not force __id";
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
    expr = (t.listOf t.int).__name;
    expected = "listOf";
  };
  flake.tests.types-identity.test-fullname-keeps-poly = {
    expr = (t.listOf t.int).name;
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
      shape = builtins.match "type:[0-9a-f]{64}" t.int.__id != null;
      length = builtins.stringLength t.int.__id;
    };
    expected = {
      shape = true;
      length = 69;
    };
  };
  flake.tests.types-identity.test-typeEq-same-structural-name = {
    # two independently-constructed listOf<int> are intensionally equal
    expr = t.typeEq (t.listOf t.int) (t.listOf t.int);
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
    expr = t.typeEq (t.listOf t.int) (t.listOf t.str);
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
      controlDistinct = t.typeEq (t.listOf t.int) (t.listOf t.str);
      controlSame = t.typeEq (t.listOf t.int) (t.listOf t.int);
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
      listOfStructs = t.typeEq (t.listOf (t.struct "cfg" { a = t.int; })) (
        t.listOf (t.struct "cfg" { a = t.str; })
      );
      attrsOfEnums = t.typeEq (t.attrsOf (t.enum "e" [ "a" ])) (t.attrsOf (t.enum "e" [ "b" ]));
      tupleOfStructs = t.typeEq (t.tuple [ (t.struct "cfg" { a = t.int; }) ]) (
        t.tuple [ (t.struct "cfg" { a = t.str; }) ]
      );
      # A composite over a SEALED member is sealed too: no preimage over it is total, so
      # it refuses rather than minting over the part it can see.
      composingASealedMember = regimeOf (t.listOf (t.refined t.int r.positive));

      # ★★ AND THE SEALED ARM'S PRECISION TRAVELS THE SAME WAY — the exact mirror of the
      # defect above, pinned on the SHIPPED constructors rather than on a fixture. Two
      # IDENTICAL `refined` constructions compare UNEQUAL: the sealed arm compares reified
      # records, `check` is a bare lambda rebuilt per call, and ADR-0034 declares that
      # precision an allocation artefact. One sealed member then de-reflexivises the whole
      # tree above it, at any depth. So this landing is two-directional — collisions
      # removed, and reflexivity-over-construction lost wherever the closure is sealed —
      # and `controlEqualMembers` below is what keeps that from reading as a broken
      # relation: over MINTED members the same composites still compare equal.
      refinedSelf = t.typeEq (t.refined t.int r.positive) (t.refined t.int r.positive);
      listOfRefinedSelf = t.typeEq (t.listOf (t.refined t.int r.positive)) (
        t.listOf (t.refined t.int r.positive)
      );

      # CONTROL: composites over EQUAL members still compare equal, so this is a finer
      # relation and not a broken one.
      controlEqualMembers = t.typeEq (t.listOf (t.struct "cfg" { a = t.int; })) (
        t.listOf (t.struct "cfg" { a = t.int; })
      );
    };
    expected = {
      listOfStructs = false;
      attrsOfEnums = false;
      tupleOfStructs = false;
      composingASealedMember = "unmintable:listOf";
      refinedSelf = false;
      listOfRefinedSelf = false;
      controlEqualMembers = true;
    };
  };

  # The three regimes are decided BY CONSTRUCTOR at the declaration, never by inspecting a
  # value — and the decision is the MINT'S: `args` either encodes totally or the encoder
  # refuses it by name. So the sealed rows are sealed for a stated reason (a caller lambda
  # in the arguments) rather than by a list in the library that could drift.
  #
  # ★ `struct` is the per-component reading paying out: the SAME constructor mints without
  # a caller `verify` and seals with one, so one struct's extra invariant does not drag
  # every struct onto the comparison limb.
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
      listOf = regimeOf (t.listOf t.int);
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
      structWithCallerVerify = "unmintable:struct";
      refined = "unmintable:refined";
      callerTypedef = "unmintable:typedef";
    };
  };

  # A sealed construction gets NO identity and a NAMED refusal when one is demanded — the
  # refusal being reachable is what rules out the alternative of dropping `__id`, which
  # would trade a detonation for a silent missing attribute. These are the SHIPPED
  # constructors rather than fixtures, so the cell fails if a constructor quietly starts
  # minting over a partial preimage.
  flake.tests.types-identity.test-sealed-constructions-refuse-when-an-identity-is-demanded = {
    expr = {
      refined = evaluates (t.refined t.int r.positive).__id;
      structWithCallerVerify = evaluates ((t.struct "s" { }).override { verify = _: null; }).__id;
      callerTypedef = evaluates (t.typedef "port" (v: v > 0)).__id;
      # CONTROL, same run: the same demand on a minted checker returns a kind-tagged
      # identity cleanly, so these refusals are the sealed regime and not a broken mint.
      mintedStillAnswers =
        builtins.match "type:[0-9a-f]{64}" (t.struct "cfg" { a = t.int; }).__id != null;
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
    expr = t.typeEq (t.option t.int) (t.listOf t.int);
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
  # detonate. `__id` is the accessor for a consumer that DEMANDS an identity and
  # refuses when there is none; a consumer that decides dispatches instead.
  #
  # ★ THIS IS THE CELL THE UNEXCLUDED FORM ABORTS ON. Comparing the record whole forces
  # every field, `__id` among them, and in this regime `__id` IS the refusal — so the
  # decision detonates on the value the refusal exists to let it decide.
  flake.tests.types-identity.test-unmintable-self-eq = {
    expr = t.typeEq unmintableChecker unmintableChecker;
    expected = true;
  };

  # The refusal must stay REACHABLE for a consumer that DEMANDS an identity. This is
  # what rules out the other remedy — making `__id` absent on a sealed checker would
  # trade a detonation for a silent missing attribute and delete the named refusal.
  flake.tests.types-identity.test-unmintable-id-still-refuses-by-name = {
    expr = {
      carriesTheAccessor = unmintableChecker ? __id;
      demandingItRefuses = !(evaluates unmintableChecker.__id);
      # CONTROL: the same demand on a minted checker returns the identity cleanly.
      mintedDemandSucceeds = (mkMinted "a" "type:dddd").__id;
    };
    expected = {
      carriesTheAccessor = true;
      demandingItRefuses = true;
      mintedDemandSucceeds = "type:dddd";
    };
  };

  # CONTROL: the minted arm decides on digests and never reaches the accessor — proven
  # by poisoning it. A run where this throws means the minted arm fell through.
  flake.tests.types-identity.test-minted-arm-never-forces-id = {
    expr = {
      equal = t.typeEq (mkMintedPoisonedId "a" "type:dddd") (mkMintedPoisonedId "b" "type:dddd");
      distinct = t.typeEq (mkMintedPoisonedId "a" "type:dddd") (mkMintedPoisonedId "a" "type:eeee");
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

  # The UNMIGRATED arm stays live for a FOREIGN record — one this library did not build,
  # or one built before the producer landed — and nothing gen-types constructs is one any
  # more, so without this fixture the arm has no subject and reads green as silence.
  flake.tests.types-identity.test-unmigrated-arm-still-decides-on-name = {
    expr = {
      sameName = t.typeEq (unmigratedChecker "foo") (unmigratedChecker "foo");
      differentName = t.typeEq (unmigratedChecker "foo") (unmigratedChecker "bar");
      # CONTROL: a stamped checker on one side leaves the arm — the pair is no longer
      # both-unmigrated, so it falls to the whole-record comparison rather than to a name
      # match against a minted value.
      mixedWithMinted = t.typeEq (unmigratedChecker "int") t.int;
    };
    expected = {
      sameName = true;
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
}
