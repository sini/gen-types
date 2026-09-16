# THE STANDALONE ROOT ENTRY — the plain-import path, which no other cell in this suite reaches.
#
# ★★★ WHY THIS FILE EXISTS: THE CLASS HAS FIRED FIVE TIMES IN ONE DAY. Every suite here builds the
# library by importing `../lib` directly with injected values, so the ROOT `default.nix` — the entry
# a non-flake consumer actually uses — is evaluated by nothing. A shim can therefore name fewer
# arguments than the library it delegates to, promise lockstep with the flake in its own comment,
# and stay green forever. That is exactly what happened here: `lib/default.nix` grew a second
# formal, the flake output was updated, the shim was not, and `import ./.` threw
# `called without required argument 'identity'` while every cell passed.
#
# ★★ THE CELL IS PURE, AND THE PURITY IS A CONSEQUENCE OF HOW IT IS CALLED. The shim's defaults
# `builtins.fetchTree` the flake-locked revs; supplying BOTH formals explicitly means those defaults
# are never forced, so this reaches the network not at all. What it tests is the shim's SIGNATURE
# and its delegation — which is precisely where the defect lives.
#
# ★ IT CATCHES BOTH DIRECTIONS OF THE DRIFT, which is why it is an argument-passing cell rather than
# an `attrNames` comparison alone:
#   · a shim naming FEWER formals than `lib` refuses this application by name
#     (`called with unexpected argument 'identity'`);
#   · a shim that forwards fewer than `lib` requires refuses inside it
#     (`called without required argument 'identity'`).
# Both are uncatchable evaluator refusals, so either turns this cell radioactive rather than failing — a crash is
# the loudest reading available and is the right one for an entry point that does not exist.
{
  genTypes,
  prelude,
  identity,
  lib,
  ...
}:
let
  # ★ ONE binding, read by BOTH cells. Duplicating the literal makes the control guard its own copy
  # and nothing else — measured: main copy broken ⇒ 2/2 exit 0 on a tree carrying a real member.
  needle = ''}/lib"[[:space:]]*\{'';

  # The same construction `ci/tests/purity.nix` uses, over the same file, for the same stated reason.
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # ★★ THE ARGUMENT SET IS BOUND ONCE, AND BOTH THE APPLICATION AND THE TOTALITY CELL READ THIS
  # BINDING — `needle`'s rule above, carried to the argument set. Two literals spelled the same are
  # TWO PREDICATES, and the totality cell would then be comparing the shim against a copy nothing
  # applies.
  entryArgs = {
    inherit prelude identity;
    # ★ THE SEAM IS `src`, AND IT IS PATH-SHAPED. The `throw` is what makes non-hermeticity
    # IMPOSSIBLE for this application rather than merely detected. `dep` is closed the same way, so
    # neither the fetch nor the build side can be reached through the defaults this cell overrides.
    inputs = { };
    src = segs: throw "the entry cell must not fetch: ${builtins.concatStringsSep "." segs}";
    dep = segs: throw "the entry cell must not build: ${builtins.concatStringsSep "." segs}";
    # ★ `wire` IS THE THIRD SEAM AND IT IS CHOSEN, NOT CLOSED. This cell's `standalone` reaches
    # `./lib` the same way the shim's own default does — `entryArgs` supplies real `prelude`/
    # `identity` values, so `wire`'s own body never forces `resolve` or reads `deps` past what those
    # two carry.
    wire = { deps, resolve }: import ../../lib deps;
  };

  standalone = import ../.. entryArgs;

  # ★★ THE READER IS BOUND, NOT ITS READING, AND THAT IS THE FIRST CONJUNCT OF THE ARMING RULE
  # RATHER THAN THE WHOLE OF IT. A bound READING (`shimFormals = builtins.attrNames
  # (builtins.functionArgs (import ../..))`) has no free parameter, so its control has nowhere else
  # to exercise it and can only re-assert the main arm's own value: MEASURED, that shape reads
  # `10/10 successful, exit 0` under the very tamper it exists to catch. Binding the READER is what
  # makes the control's DIFFERENT INPUT expressible at all.
  formalsOf = f: builtins.attrNames (builtins.functionArgs f);

  # ★ THE SECOND NEEDLE, bound once and read by both arms below for the same reason `needle` is.
  # `[[:space:]]*` spans the newline a formatter may put between `../..` and `{`. It does not match
  # `formalsOf (import ../..)` (a `)` follows, not a `{`) nor `import ../../examples/…` (a `/`
  # follows), so the one thing it counts is an entry application to a literal.
  entryNeedle = ''\.\./\.\.[[:space:]]*\{'';
  countEntry =
    text: builtins.length (builtins.filter builtins.isList (builtins.split entryNeedle text));

  # ★★ THE SEAM-CLOSING ARGUMENT SET FOR THE HERMETIC PAIR AT THE FOOT OF THIS FILE, BOUND RATHER
  # THAN WRITTEN AT THE APPLICATION — `entryArgs`' own rule, for `entryNeedle`'s reason. `dep` stops
  # the resolver at the PATH instead of fetching it, and replacing `wire` publishes the whole record
  # the shim's body hands TO `wire` — its `deps` half is the attrset `./lib` receives only while
  # `wire`'s own default is `{ deps, resolve }: import ./lib deps`, which the cell at the foot of
  # this file is what holds, and its `resolve` half is the shim's own `follows` rule, which is why
  # nothing below transcribes that rule. So this application is hermetic by CONSTRUCTION. Nothing
  # else is supplied: every dependency formal is left at its default, which is the point — the
  # defaults are the subject.
  pathArgs = {
    dep = segs: segs;
    wire = args: args;
  };
  seam = import ../.. pathArgs;
  paths = seam.deps;

  # ★★★ THE SHIM'S OWN RESOLVER, READ RATHER THAN RETRANSCRIBED. `default.nix` holds the ONE
  # declaration of the `follows` rule in this library and publishes it in the record its body hands
  # to `wire`; this is that binding and not a copy of it. So the fixture control below drives the
  # expression the shim itself resolves with, and `…-defaults-to-its-own-node` resolves the shim's
  # declared paths by the shim's own rule rather than by a second copy that can agree with its own
  # expectation while both are wrong.
  shimResolve = seam.resolve;

  # ★ THE ci LOCK, READ AS PURE DATA — and the rule that walks it is NO LONGER TRANSCRIBED HERE:
  # `shimResolve` above IS `default.nix`'s binding. A direct edge IS the node key; a `follows` value
  # is a PATH resolved segment by segment from this lock's own root. Never `lock.nodes.<label>` — a
  # last-segment shortcut reads a DIFFERENT node, and a ci lock routinely carries several same-named
  # ones. Reading the lock is pure data; nothing here fetches.
  lock = builtins.fromJSON (builtins.readFile ../../flake.lock);

  # ★★ THE RESOLVER IS BOUND OVER ITS LOCK, AND THAT IS WHAT MAKES ITS CONTROL EXPRESSIBLE AT ALL. A
  # `repoOf` closed over THIS lock has no free parameter, so a control could only re-assert the main
  # arm's own value; taking the lock as an argument is what puts the control AT AN INPUT THE MAIN ARM
  # DOES NOT USE. `shimResolve` takes its lock the same way and for the same reason — which is why
  # `default.nix` publishes the LOCK-PARAMETERISED rule rather than its own applied `fetch`. The
  # `lock` formal here deliberately shadows the binding above.
  #
  # ★★★ AND THE CONTROL IS NOT CEREMONY, IT IS THE ENTIRE ORACLE FOR THIS RULE — which this library
  # declares EXACTLY ONCE, in `default.nix`, so *this rule* now names one expression and not two.
  # A hermetic fixture is the only thing that can discriminate a resolver against this library's own
  # lock: unlike gen-settings' `prelude` edge, BOTH of this library's direct edges already resolve to
  # a node matching their own label (`prelude` → node `gen-prelude`, `identity` → node `gen-identity`),
  # so nothing on this library's OWN lock distinguishes the fold from the `lock.nodes.<label>`
  # shortcut — it is the fixture below that drives the SHIM's binding: with that shortcut written
  # into `default.nix`'s `resolve`, the control below reds.
  repoOf = lock: segs: lock.nodes.${shimResolve lock segs}.locked.repo;

  # ★ THE FIXTURE LOCK, AND IT IS TWO CLAIMS IN ONE SHAPE. `root → a` is a DIRECT edge, where the
  # value IS the node key; `a-node → b` is a `follows` PATH resolved from the lock's own root — so
  # both branches of `following` are exercised. Walking `[ "a" "b" ]` lands on `the-walked-node`;
  # indexing the last segment lands on the unrelated node keyed `b`. The two rules disagree BY
  # CONSTRUCTION, which is what makes the control total over every library rather than over the ones
  # whose own lock happens to disagree. It is a literal: nothing here reads a file or fetches.
  followsFixture = {
    root = "root";
    nodes = {
      root.inputs = {
        a = "a-node";
        elsewhere = "the-walked-node";
      };
      a-node.inputs.b = [ "elsewhere" ];
      the-walked-node.locked.repo = "gen-walked";
      b.locked.repo = "gen-indexed";
    };
  };

  # ★★ THE SHIM'S `wire` DEFAULT, COUNTED AS TEXT. `[[:space:]]` spans the newline a formatter may
  # put anywhere inside the default, and COMMENTS ARE STRIPPED FIRST — load-bearing here rather than
  # prophylactic, because the shim's own prose quotes this default, so an unstripped scan keeps
  # reading 1 on a file whose CODE has been rewired. Bound once and read by BOTH cells below: two
  # literals spelled the same are two predicates, and the control would then guard only its own copy.
  wireNeedle = ''wire[[:space:]]*\?[[:space:]]*[{][[:space:]]*deps[[:space:]]*,[[:space:]]*resolve[[:space:]]*[}][[:space:]]*:[[:space:]]*import[[:space:]]+\./lib[[:space:]]+deps[[:space:]]*,'';
  countWire =
    text:
    builtins.length (
      builtins.filter builtins.isList (
        builtins.split wireNeedle (
          builtins.concatStringsSep "" (builtins.filter builtins.isString (builtins.split "#[^\n]*" text))
        )
      )
    );
in
{
  # ★ The assertion is over the APPLIED surfaces, not over the entries themselves: both are
  # functions of their injected substrate, and two Nix lambdas are never equal — so
  # `entry == entry` would read `false` on a correct library and could not distinguish drift from
  # the language. The applied form is also the stronger claim: it is the surface a consumer
  # actually receives.
  flake.tests.entry.test-standalone-entry-matches-lib = {
    expr = builtins.attrNames standalone;
    expected = builtins.attrNames genTypes;
  };

  # The surface is not merely equal but non-trivial, so the cell above cannot pass by both sides
  # being empty.
  flake.tests.entry.test-control-the-compared-surface-is-non-trivial = {
    expr = builtins.length (builtins.attrNames standalone) > 20;
    expected = true;
  };

  # ★ THE COMPARISON IS SHOWN ABLE TO FAIL, in the same run. Without this, an `attrNames` equality
  # between two values that happen to be the same import is a tautology nobody has checked.
  flake.tests.entry.test-control-the-comparison-discriminates = {
    expr = builtins.attrNames standalone == builtins.attrNames (removeAttrs genTypes [ "int" ]);
    expected = false;
  };

  # And the library reached THROUGH the shim actually works, rather than merely having the right
  # keys — a delegation that forwarded the wrong value would satisfy an `attrNames` check.
  flake.tests.entry.test-the-shims-library-is-live = {
    expr = standalone.int.check 5 "the-value";
    expected = "the-value";
  };

  # ★ THE FOUR CELLS ABOVE CANNOT SEE THIS CLASS, and the reason is the property that makes them
  # hermetic: they supply every dependency formal explicitly, so the shim's `fetch`-backed DEFAULTS —
  # which is where the divergence lives — are never forced. Forcing them would put `builtins.fetchTree`
  # inside the suite. This cell reads the CONSTRUCTION instead of the outcome, which is strictly wider:
  # it also catches the member that never throws (a defaulted formal on the far side turns the loud arm
  # of the class silent) and the member that has not yet drifted.
  #
  # ★★ COMMENTS ARE STRIPPED FIRST, AND THAT IS LOAD-BEARING RATHER THAN TIDY. `ci/tests/purity.nix`
  # states the same property for the same reason and over this same file (`stripComments (builtins.readFile
  # ../../default.nix)`): the house convention for a FIXED member is a comment explaining why not `/lib`,
  # and a raw scan reds on that comment while the file is correct. MEASURED, in-suite, on a tree whose
  # member had just been fixed — with a comment PLANTED in the house idiom, because no live site reds
  # today: every existing such comment happens to write `` `./lib` `` (relative, uninterpolated), and
  # raw ≡ stripped across all 14 domain files at HEAD. The strip is PROPHYLACTIC, and that is the
  # point — it stops the next correctly-written comment from reddening a correct file.
  #
  # ★ `[[:space:]]*` spans the newline a formatter may put between `/lib"` and `{` — measured: a
  # line-anchored form misses exactly that.
  #
  # ★★ THE NEEDLE IS BOUND ONCE AND BOTH CELLS READ THAT BINDING. Two literals spelled the same are
  # TWO PREDICATES, and the control would then guard only its own copy: MEASURED — with the needle
  # duplicated, breaking the MAIN copy by one character gave `2/2 successful, exit 0` over a tree
  # carrying a real member, with the control still ✅ in the same run. That is §1.5's class — a second
  # signature nothing compares against the first — committed by the instrument built to detect it.
  # With the shared binding the same one-character break REDS THE CONTROL.
  #
  # ★ A bare `.../lib` with NO argument set is EXCLUDED, and the exclusion is a claim about the FAR SIDE
  # AT ITS PIN rather than about this file: it holds only while the target's `lib` is a value. All
  # nineteen such sites in this domain reach gen-prelude / gen-identity / gen-algebra, each measured
  # `"set"` 2026-08-29. It is NOT a property of the spelling — `den-hoag-jhsb` measured
  # `select ? import "${fetch "gen-select"}/lib"` in gen-pipe yielding a LAMBDA (gen-select's `lib` takes
  # `{ algebra }`), a silent member this predicate does not count — and this cell cannot observe its own
  # premise going false. See §4.4.
  flake.tests.entry.test-no-dependency-is-built-past-its-own-entry =
    let
      parts = builtins.split needle (stripComments (builtins.readFile ../../default.nix));
    in
    {
      # ★ THE ASSERTION IS ON THE COUNT. `reaches` is a diagnostic so a failure names the dependency,
      # but it is derived by a second match that a non-`fetch` spelling defeats — asserting on names
      # alone would read `[ ]` on a real member and pass.
      expr = {
        count = builtins.length (builtins.filter builtins.isList parts);
        # ★ THE REACH IS NAMED BY THE CLOSING `]` OF THE ROSTER-KEY LIST SEGMENT, NOT BY A `fetch`
        # CALL — the arm-B shim never spells `fetch "gen-x"` in its text at all; the dependency name
        # appears only inside the `dep [ "gen-x" ]` segment list the seam's own default threads
        # through `resolve`. `[[:space:]]*` spans the newline a formatter may put before `]`.
        reaches = map builtins.head (
          builtins.filter (m: m != null) (
            map (p: builtins.match ''.*"(gen-[a-z-]+)"[[:space:]]*]$'' p) (
              builtins.filter builtins.isString parts
            )
          )
        );
      };
      expected = {
        count = 0;
        reaches = [ ];
      };
    };

  # ★★ THE DETECTOR IS SHOWN ABLE TO FIRE, IN THE SAME RUN, ON THE SAME PREDICATE — `purity.nix`'s
  # standing rule and `den-hoag-e421`'s landed remedy. Without it, `count = 0` is equally consistent
  # with a needle that cannot match: MEASURED — one character changed in the needle reads
  # `{ count = 0; reaches = [ ]; }` on a file carrying three real members, i.e. byte-identical to this
  # cell's own `expected`. The planted member is REFLOWED, so it also pins the `[[:space:]]*` span.
  flake.tests.entry.test-control-the-entry-shape-check-discriminates = {
    expr = builtins.length (
      builtins.filter builtins.isList (
        builtins.split needle (stripComments ''
          {
            graph ? import "''${fetch "gen-graph"}/lib"
              { inherit prelude; },
          }: null
        '')
      )
    );
    expected = 1;
  };
  # ★★★ THE HERMETICITY OF THIS CELL BECOMES AN INVARIANT HERE, AND IT TAKES TWO CELLS BECAUSE THEY
  # ANSWER DIFFERENT QUESTIONS. Everything above is offline only because the argument set happens to
  # supply every `fetch`-backed formal, and that was a property of the file's TEXT which nothing
  # asserted. MEASURED before these two cells existed: with the bare form seeded and nothing else
  # touched, the whole entry suite passed, exit 0. The broken state looked exactly like the correct
  # one, which is why the property needs an invariant rather than one more reading of it.
  #
  # ★★ THE SEMANTIC INSTRUMENT CANNOT CARRY A FILE-LEVEL CLAIM, and that is measured rather than
  # argued: with this totality cell in place and the application rewritten to a literal, the totality
  # cell reads GREEN — it is still checking a binding that nothing applies — and the `fetch` throw
  # goes with the argument set that carried it. The structural cell below is the only detector left,
  # which is why neither cell is ceremony for the other.
  #
  # ★★ THE OBLIGATION IS TOTAL — every formal the shim DECLARES, never "the `fetch`-backed ones" and
  # never "the harmless defaults". "Harmless" is not a property of a formal but of its DEFAULT
  # EXPRESSION, which changes without notice: `lock` is the most obviously harmless formal on this
  # roster and it is the source of every fetch coordinate in the shims that declare it. A rule that
  # supplied only the fetch-backed formals would have to re-derive harmlessness at every shim edit,
  # or freeze a name list — a second signature nothing compares against the first. Totality needs no
  # classification at all, so the bad state cannot form rather than being filtered after it does.
  #
  # ★ IT IS HERMETIC, MEASURED: `builtins.functionArgs` does not force defaults —
  # `builtins.functionArgs ({ a ? throw "FORCED", b }: null)` reads `{ a = true; b = false; }` with
  # no throw. Reading a signature never reaches the network.
  #
  # ★ EQUALITY, NOT CONTAINMENT, because six of the fourteen shims in this domain carry `...`: there
  # a key the shim does not declare is accepted, unread and unreported, so containment would pass a
  # stale key forever. Equality reds on it, loudly, naming it.
  flake.tests.entry.test-the-entry-application-is-total = {
    expr = formalsOf (import ../..);
    expected = builtins.attrNames entryArgs;
  };

  # ★★★ AN ARMED PAIR IS A CONJUNCTION: the two arms SHARE the operand (`formalsOf`), AND the control
  # exercises that operand AT AN INPUT THE MAIN ARM DOES NOT USE. Either half alone detects nothing,
  # and both halves were driven one variable at a time by neutering the shared operand — operand
  # spelled twice, control at a different input: `10/10`, exit 0, UNDETECTED; operand shared, control
  # moved to the main arm's own input (`formalsOf (import ../..)`): `10/10`, exit 0, UNDETECTED;
  # operand shared AND control at a different input: `9/10`, exit 1, rc 1 with one failing cell. Known-answer versus
  # relative is not the axis — a relative control at a different input catches the same tamper.
  #
  # ★ THE FIXTURE NAMES `a` AND `b`, which are the formals of a lambda THIS CELL WRITES and no shim
  # supplies. That is the different input, not an exception to "no formal OF THE SHIM is hardcoded":
  # a control written to avoid every literal name would have to reach for the shim's own formals,
  # which puts it at the main arm's input and makes it blind. Its literal expectation is convenience;
  # the different input is the mechanism.
  flake.tests.entry.test-control-the-formals-reader-discriminates = {
    expr = formalsOf (
      {
        a,
        b ? null,
      }:
      null
    );
    expected = [
      "a"
      "b"
    ];
  };

  # ★★ THE STRUCTURAL CELL — the one the semantic instrument above cannot replace, because the edit
  # that reintroduces the defect is the same edit that removes the semantic instrument. It reads THIS
  # file's own text and refuses the bare application outright, so the property survives tomorrow's
  # edit instead of describing today's.
  #
  # ★★ COMMENTS ARE STRIPPED FIRST, AND ACROSS THIS DOMAIN THAT IS LIVE RATHER THAN PROPHYLACTIC.
  # MEASURED over the fourteen files carrying this cell: three of them quote the bare application in
  # prose, so an unstripped scan reads 1 there and reds a correct file; the other eleven read 0
  # either way. The strip is what stops the next correctly-written comment — this one included —
  # from reddening the file it explains.
  flake.tests.entry.test-the-entry-is-never-applied-to-a-literal = {
    expr = countEntry (stripComments (builtins.readFile ./entry.nix));
    expected = 0;
  };

  # ★★ THE FIXTURE IS ASSEMBLED, AND THAT IS THE MECHANISM RATHER THAN A FLOURISH. The cell above
  # reads THIS FILE, unlike `needle`'s cell which reads the shim — so a fixture written as a plain
  # literal would appear in the very text the main arm scans and red it. MEASURED, both arms: the
  # assembled form's VALUE matches (1) while its own SOURCE BYTES do not (0); the naive literal's
  # source bytes match (1) and red the correct file.
  flake.tests.entry.test-control-the-literal-application-check-discriminates = {
    expr = countEntry ("  standalone = import ../" + ".. { };");
    expected = 1;
  };

  # ★★★ THE DEFAULTS THEMSELVES — the three cells below are the ones every cell above is blind to by
  # the property that makes them hermetic. `entryArgs`/`standalone` supplies every dependency formal,
  # so the shim's `ci/flake.lock`-backed defaults never fire there; nothing is supplied here.
  #
  # ★★ THE OBLIGATION IS PER DEPENDENCY PATH, NOT PER LIBRARY, and that is what splits it into
  # three. A cell that reds when ANY ONE dependency is unreachable measures a disjunction while
  # reading like a conjunction, because `builtins.deepSeq` does not enter the lambdas the rest are
  # reached from. The shim's eager body forces its dependencies at the BOUNDARY, so the third cell
  # below reaches all of them, driven per path by sealing one and resolving the rest.
  #
  # ★★ EVERY WIRED DEPENDENCY RESOLVES, AND RESOLVES TO A NODE OF ITS OWN REPOSITORY. The shim states
  # its intent as a PATH; this resolves that path through the same lock by the same rule and asks
  # which repository the node it lands on belongs to. A path repointed at a live-but-wrong dependency
  # — the failure the surface comparison above and a whole-seam seal both pass — reds here, naming
  # the formal and the repository it reached. It is HERMETIC: `pathArgs` closes `dep`, so the map is
  # read and resolved without a fetch.
  #
  # ★★ THE DOMAIN IS THE WIRED SET, NOT THE DECLARED SET — AND IT IS THE `deps` HALF OF THE RECORD
  # THE SHIM'S BODY HANDS TO `wire`, NOT THE ATTRSET `./lib` RECEIVES. The two coincide only while
  # `wire`'s own default is `{ deps, resolve }: import ./lib deps`, which is held by
  # `test-the-wire-default-is-the-librarys-own-application` below and by nothing else. A formal
  # declared and never threaded into that attrset is invisible here — a domain statement rather than
  # a gap, and `test-the-entry-application-is-total` above is where a stray DECLARED formal surfaces.
  #
  # ★ STATED CEILING: `locked.repo` is neither `owner` nor node identity. A same-named repository
  # under another owner passes, and so does a path repointed at a DIFFERENT NODE of the right
  # repository — the shim's declared path is the only statement of intent, so there is no independent
  # `expected` to compare a resolved node against. Recorded open rather than repaired.
  flake.tests.entry.test-every-wired-dependency-defaults-to-its-own-node = {
    expr = builtins.mapAttrs (_: repoOf lock) paths;
    expected = builtins.mapAttrs (formal: _: "gen-" + formal) paths;
  };

  # ★★★ THE DISCRIMINATING HALF OF THE CELL ABOVE — and for the `follows` rule it is the whole
  # oracle, not a supplement to one, because the rule has ONE declaration and `repoOf` is built over
  # it. The two arms SHARE `repoOf`, hence share `shimResolve`, hence share `default.nix`'s own
  # fold; this one exercises it AT AN INPUT THE MAIN ARM DOES NOT USE, a hand-written lock whose
  # path walk and whose last-segment shortcut land on different nodes by construction. Replace the
  # fold in `default.nix` with the shortcut and this reds; the cell above cannot be relied on to
  # catch it on this library's own lock: both of gen-types' direct edges already resolve to a node
  # matching their own label (`prelude` → node `gen-prelude`, `identity` → node `gen-identity`), so a
  # last-segment shortcut lands on the SAME node the fold does and the cell above reds at none of the
  # tampered arms the control below catches.
  flake.tests.entry.test-control-the-follows-resolver-discriminates = {
    expr = repoOf followsFixture [
      "a"
      "b"
    ];
    expected = "gen-walked";
  };

  # ★★ THE DENOMINATOR, TAKEN INDEPENDENTLY — without it the cell above is vacuous over an empty map.
  # `paths` is what the root WIRES; `functionArgs (import ../../lib)` is what the library REQUIRES,
  # read from a different file by a different builtin. A dependency dropped from the shim's body reds
  # here even if every surviving path still resolves, and a dependency the library newly requires but
  # the shim never wires reds here too.
  flake.tests.entry.test-the-wired-dependency-set-is-the-libs-own-formals = {
    expr = builtins.attrNames paths;
    expected = builtins.attrNames (builtins.functionArgs (import ../../lib));
  };

  # ★★★ THE DEFAULTS FORCED — the one cell in this file that is NOT hermetic. Forcing them IS
  # `builtins.fetchTree`: the accepted price of measuring the non-flake contract at all, and it
  # remains PURE, because `fetchTree` on a locked node is narHash-addressed with no channel and no
  # `<…>`. `builtins.seq` of the dispatched root runs the shim's eager body, which forces every wired
  # dependency to WHNF before `./lib` sees it, so a nonexistent node, an unresolvable follows path or
  # a throwing root is loud at the BOUNDARY on every path rather than wherever a consumer first
  # happens to reach one.
  #
  # ★ THE FORCE STOPS AT WHNF, DELIBERATELY: `seq` of an attrset does not force its members, so this
  # never reaches into a dependency's own surface and a member a dependency deliberately refuses to
  # build is not an exception to it.
  flake.tests.entry.test-the-defaulted-entry-forces-every-dependency =
    let
      root = import ../..;
      dispatched = if builtins.isFunction root then root { } else root;
    in
    {
      expr = builtins.seq dispatched "forced";
      expected = "forced";
    };

  # ★★★ THE SHIM'S OWN `wire` DEFAULT, AND IT IS WHAT EVERY HERMETIC CELL ABOVE RESTS ON. `paths` is
  # the `deps` half of the record the shim's body hands to `wire` — it is the attrset `./lib`
  # RECEIVES only while `wire`'s own default is `{ deps, resolve }: import ./lib deps`, and no cell
  # above reads that default: the two hermetic cells REPLACE `wire` with `args: args`, the forcing
  # cell stops at WHNF of whatever `wire` returned, and the surface cell compares `attrNames`, which
  # `./lib`'s structure fixes independently of its arguments.
  #
  # ★★ THE READING IS IRREDUCIBLY TEXTUAL, AND THAT IS THE SEAM'S OWN REASON FOR EXISTING: Nix
  # publishes WHETHER a formal has a default and never WHAT it is, so there is no semantic
  # construction to compare against. It is the same argument
  # `test-the-entry-is-never-applied-to-a-literal` carries in this domain — the edit that
  # reintroduces the defect is the same edit that would remove any semantic instrument for it.
  flake.tests.entry.test-the-wire-default-is-the-librarys-own-application = {
    expr = countWire (builtins.readFile ../../default.nix);
    expected = 1;
  };

  # ★★★ THE DISCRIMINATING HALF, IN THREE ARMS BECAUSE THE PREDICATE HAS THREE WAYS TO BE DEAD. Both
  # cells read the one `countWire` binding, and this one exercises it AT AN INPUT THE MAIN ARM DOES
  # NOT USE — assembled fixtures, never `../../default.nix`. `exact` proves it can count the real
  # default at all; `rewired` proves it refuses the one-token corruption the main arm exists to
  # catch; `commented` proves the comment strip is LIVE, and that arm is the sharp one — the same
  # text unstripped reads 1, which is precisely the false green a scan of a self-documenting shim
  # would otherwise return.
  flake.tests.entry.test-control-the-wire-default-check-discriminates = {
    expr = {
      exact = countWire "wire ? { deps, resolve }: import ./lib deps,";
      rewired = countWire ''wire ? { deps, resolve }: import ./lib (deps // { x = throw "no"; }),'';
      commented = countWire ''
        # wire ? { deps, resolve }: import ./lib deps,
        wire ? { deps, resolve }: import ./lib (deps // { }),
      '';
    };
    expected = {
      exact = 1;
      rewired = 0;
      commented = 0;
    };
  };

  # ★★★ CHANNEL 2 — THE `inputs` OVERRIDE BAG. The shim declares three channels and one precedence:
  # a named formal wins, the bag is next, tested by attrset membership, and the ci lock is the
  # default. Every cell above exercises the LOCK, so a formal transcribed as `x ? dep [ … ]` instead
  # of `x ? inputs.gen-x or (dep [ … ])` leaves its override silently ignored. ★ It matters most where
  # the flake arm is UNAPPLIED — the root published as `import ./.` rather than applied — because
  # there the bag is the ONLY override path a consumer has.
  #
  # ★★ TOTAL OVER THE WIRED SET BY CONSTRUCTION. `expr` and `expected` are both derived from
  # `paths`, so the domain is whatever the root wires and never a hand-written list, and the
  # denominator is taken independently by `…-is-the-libs-own-formals`, so an empty map cannot read as
  # a pass. The sentinels are DISTINCT per formal, so a bag key wired to the wrong formal reds too.
  # It is hermetic: `pathArgs` closes `dep`, and with every formal overridden no default is reached.
  flake.tests.entry.test-the-inputs-bag-overrides-every-wired-default =
    let
      overrides = builtins.mapAttrs (formal: _: "the ${formal} override, from the inputs bag") paths;
      bag = builtins.listToAttrs (
        map (formal: {
          name = "gen-" + formal;
          value = overrides.${formal};
        }) (builtins.attrNames paths)
      );
    in
    {
      expr = (import ../.. (pathArgs // { inputs = bag; })).deps;
      expected = overrides;
    };
}
