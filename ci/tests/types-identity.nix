# gen-types: checker identity — __name, __id, and conservative equality (typeEq /
# conservativeEq), which dispatches on the checker's identity REGIME.
{ genTypes, ... }:
let
  t = genTypes;

  # Fixtures for the two regimes a producer stamps. Every SHIPPED checker carries no
  # `__mint` and is therefore unmigrated, which is why the cells below are the only
  # ones that exercise the other two arms.
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
  flake.tests.types-identity.test-id-is-sha256-hex = {
    expr = builtins.stringLength t.int.__id;
    expected = 64;
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

  # ── conservative equality by identity REGIME ────────────────────────────────
  # Every cell above exercises the UNMIGRATED arm: no producer stamps `__mint` on a
  # checker yet, so `typeEq` is name equality there and their answers are unchanged.
  # The cells below cover the two regimes a producer stamps, so the dispatch is
  # asserted BEFORE its producer lands rather than after.

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

  flake.tests.types-identity.test-conservativeEq-is-typeEq-on-every-regime = {
    expr = {
      unmigrated = t.conservativeEq t.int t.int == t.typeEq t.int t.int;
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
