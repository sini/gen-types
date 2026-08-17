# Purity invariant for gen-types: lib/ is nixpkgs-lib-free.
#
# The pure structural checker must never re-acquire a nixpkgs.lib tether or reach
# into the module-system tier. This test pins "pure" as a checked property — a
# stray `lib.`/`lib.types`/`evalModules`/`mkOption`/`nixpkgs` creeping into the
# component source fails CI.
#
# ci/ itself legitimately uses nixpkgs lib (this scanner included); only lib/
# is in scope. The scan is factored out so we can also prove it has TEETH by running
# it against an injected violation and asserting it is caught.
#
# Every label this scanner emits is a repo-root-relative path — never a bare basename, and
# never a path value. A path value renders as the store copy the flake is evaluated from
# (`/nix/store/<hash>-source/lib/checkers.nix`), which names a file no reader can open in
# their own checkout and whose hash moves on any unrelated source edit; a red CI's only
# product is its message, so a label that decays that way costs the whole cell. A bare
# basename fails the other way, by collision: this repository holds both `lib/default.nix`
# and a root `default.nix`, and it would name a file under a lib/ subdirectory with the same
# string as its sibling at the top. The walk therefore carries a prefix down from the root it
# is handed and builds each label out of it, so there is no remaining place where a label
# could be constructed any other way.
#
# The reach of the scan — every `.nix` file under lib/, at any depth — is a separate property
# and rests on a separate mechanism: it follows from the walk descending, not from how the
# walk names what it finds. lib/ is flat today, so nothing here exercises that descent.
{ genPrelude, lib, ... }:
let
  typesDir = ../../lib;

  # Drop everything from the first `#` on each line (safe: `#` appears only in
  # comments across these files — no `#` in any string literal).
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  # walk : string -> path -> [ { name; path; } ], `name` being `prefix` extended by the
  # entry's own position in the tree — so a violation is reported at a path a reader can act
  # on, rather than at the store path the sources happen to be evaluated from. A subdirectory
  # extends the prefix it was given rather than replacing it.
  walk =
    prefix: dir:
    lib.concatLists (
      lib.mapAttrsToList (
        entry: type:
        if type == "directory" then
          walk "${prefix}${entry}/" (dir + "/${entry}")
        else if lib.hasSuffix ".nix" entry then
          [
            {
              name = "${prefix}${entry}";
              path = dir + "/${entry}";
            }
          ]
        else
          [ ]
      ) (builtins.readDir dir)
    );

  # Tokens signalling a nixpkgs-lib tether or the module-system tier.
  forbidden = [
    "lib."
    "lib.types"
    "{ lib }"
    "{ lib,"
    "evalModules"
    "mkOption"
    "nixpkgs"
  ];

  # scan : [ { name; code; } ] -> [ "file: 'tok'" ]
  scan =
    sources:
    lib.concatMap (
      src:
      map (tok: "${src.name}: '${tok}'") (lib.filter (tok: genPrelude.hasInfix tok src.code) forbidden)
    ) sources;

  # read : [ { name; path; } ] -> [ { name; code; } ]. Factored out so the fixture cell below can
  # run the same pipeline the library scan runs, rather than a second copy of it.
  read =
    entries:
    map (e: {
      inherit (e) name;
      code = stripComments (builtins.readFile e.path);
    }) entries;

  realSources = read (walk "lib/" typesDir);

  # The live counterpart to `forbidden`: a token this library genuinely contains, at the exact
  # labels where it genuinely occurs. `check` sits in four of the five sources and is absent from
  # `lib/validate.nix`, which is the validator base (`mkValidator` / `runValidators` /
  # `formatErrors`) — the one file here about validators rather than checkers. That single
  # exclusion is what gives the expectation its teeth: the list is a PROPER subset of the tree,
  # so a read collapsed to one fixed text lands outside it either way — carrying the token the
  # list swells to all five, not carrying it the list collapses toward empty.
  #
  # The list is derived POST-STRIP, which is not what a plain `grep -lF check lib/*.nix` reports:
  # that matches five of five, because `lib/validate.nix` names the token in a comment.
  liveToken = "check";
  liveReads = map (s: s.name) (lib.filter (s: genPrelude.hasInfix liveToken s.code) realSources);

  # A synthetic poisoned source — NOT written to disk, so the real scan stays green while we
  # prove the detector actually fires. Its label is bracketed so it cannot be read as one of the
  # repo-root-relative paths it now sits beside.
  poisoned = {
    name = "<injected>";
    code = stripComments "  foo = lib.types.str; # comment mentioning nixpkgs is stripped";
  };
in
{
  # The real component source is clean. That `[ ]` is not evidence on its own — a scan that read the
  # wrong tree, or no tree, or every file as one fixed string produces it just as readily. The two
  # cells below are what make it mean something: the manifest pins WHICH files this list holds, and
  # the live-content cell pins that those labels carry their files' text.
  flake.tests.types-purity.test-library-source-is-dependency-free = {
    expr = scan realSources;
    expected = [ ];
  };

  # Which files the scan reads, written down as the literal list. Disconnection is an identity
  # defect and non-emptiness is a cardinality predicate, so the two do not meet: a scan that had
  # dropped the whole library tree and kept some other file would still be non-empty, would still
  # have non-empty content, and would still report the invariant clean over a set containing none
  # of the library. Only a statement about which files are read can see that.
  #
  # Writing the membership down also means a new library file arrives as a RED rather than being
  # absorbed silently. That is the point rather than the price — the scope of an invariant is a
  # declared surface, not a default.
  #
  # This cell is silent on content: a read handing every entry one fixed string satisfies it
  # exactly. The live-content cell below is the half that sees that.
  flake.tests.types-purity.test-scan-subject-is-the-library-tree = {
    expr = map (s: s.name) realSources;
    expected = [
      "lib/checkers.nix"
      "lib/default.nix"
      "lib/refined.nix"
      "lib/strict.nix"
      "lib/validate.nix"
    ];
  };

  # And that those labels carry their files' text. The cell above reports `[ ]` just as readily
  # for a read that returned one fixed string for every entry as for a library that is clean, and
  # it cannot tell those apart on its own: its expectation is an absence, and a scan of constants
  # produces nothing to find. So the reads are pinned here in the same shape the tree is pinned in
  # — an exact list, not a count — asked of a token that is genuinely present rather than
  # genuinely absent. Content is one axis of the subject; membership — which files are read at all
  # — is the other, and the manifest above states it. The two together are what pin the subject,
  # and neither does it alone.
  #
  # That pair is what the library cell and the welded detector cell below both lean on: each of
  # them claims an absence over text read from disk, and no such claim is evidence while the
  # subject it is made over could be empty or constant.
  #
  # `lib/validate.nix` is outside this list BY CONSTRUCTION — that is what makes the list
  # discriminate — so a mutation that replaces only that file's text is seen by no cell here.
  flake.tests.types-purity.test-scan-reads-are-live = {
    expr = liveReads;
    expected = [
      "lib/checkers.nix"
      "lib/default.nix"
      "lib/refined.nix"
      "lib/strict.nix"
    ];
  };

  # The residual content floor. The live list above is a PROPER subset of the manifest, which is
  # what lets it discriminate a constant-returning read in both directions — and the file it leaves
  # out is `lib/validate.nix`, whose text no other cell here pins. A mutation replacing only that
  # file's text is seen by nothing else: the manifest stays green because the name is intact, the
  # live list stays green because that label was never in it, and the library cell stays green
  # because the replacement carries no forbidden token.
  #
  # This cell closes the empty case for that residue and no more. It is not a claim that the suite
  # is non-vacuous — the manifest and the live list are what carry that — and a non-empty constant
  # substituted for the residue file's text still passes here.
  #
  # The `!= [ ]` conjunct guards this cell's OWN vacuity and is not redundant with the manifest:
  # `lib.all` over an empty list is vacuously true, so without it the floor would report clean on
  # exactly the degeneracy it exists to bound.
  flake.tests.types-purity.test-scan-reads-non-empty-sources = {
    expr = realSources != [ ] && lib.all (s: s.code != "") realSources;
    expected = true;
  };

  # The detector has teeth, and it grows them on the real subject: the scan runs over exactly the
  # source list the library cell scans, with one synthetic entry appended. So the firing is proven
  # by the same call that reports the tree clean, and the expectation states both halves at once —
  # the library contributes nothing and the planted tether contributes precisely this.
  #
  # That first half is an absence claim about text read from disk, so this cell's green is
  # evidence only while something else holds the subject. The manifest and the live-content cell
  # above are what hold it, on their two axes: under a read collapsed to a constant this
  # expression reduces to `scan [ poisoned ]`, which is the expectation exactly, and this cell
  # would pass a fortiori — the live-content cell is what sees that, and the manifest is what sees
  # a subject swapped for some other tree.
  #
  # The expectation is the violation LIST rather than merely that one was produced. A detector
  # firing on the wrong token, or whose `file: 'tok'` message has decayed into something a reader
  # cannot act on off a red CI, is broken in the way that matters, and non-emptiness passes both.
  # The list form couples this cell to `forbidden` deliberately — adding a token the payload above
  # matches reds it — so that the teeth are looked at whenever the teeth change.
  flake.tests.types-purity.test-detector-catches-injected-violation = {
    expr = scan (realSources ++ [ poisoned ]);
    expected = [
      "<injected>: 'lib.'"
      "<injected>: 'lib.types'"
    ];
  };

  # The walk descends, and carries its prefix while doing so. lib/ is flat, so the recursive branch
  # never runs against the real tree and a walk that quietly stopped descending would keep every
  # other cell here green. The fixture tree is nested on purpose and carries a planted tether at
  # each of its two depths. Handing it its own real position in the repository as the prefix pins
  # both halves of the naming rule at once: the prefix the walk is GIVEN is threaded through, and
  # the prefix it BUILDS for a subdirectory extends that one rather than replacing it.
  #
  # The fixtures live under `_fixtures/` because the test-tree importer ignores paths with a
  # component beginning with an underscore, so they are never imported as tests. Their tethers are
  # planted deliberately and sit outside the purity scan's subject, which is lib/ alone — they
  # cannot trip the library cell.
  #
  # Unlike the absence cells here, this one arms itself and composes with nothing: its expectation
  # is a non-empty list over its own subject, so a read that was severed or emptied makes the
  # actual `[ ]` and reds it.
  flake.tests.types-purity.test-walk-descends-into-subdirectories = {
    expr = scan (read (walk "ci/tests/_fixtures/purity-walk/" ./_fixtures/purity-walk));
    expected = [
      "ci/tests/_fixtures/purity-walk/nested/tethered.nix: 'lib.'"
      "ci/tests/_fixtures/purity-walk/nested/tethered.nix: 'lib.types'"
      "ci/tests/_fixtures/purity-walk/surface.nix: 'mkOption'"
    ];
  };

  # And it does not "catch" a token that only appears inside a comment.
  flake.tests.types-purity.test-comments-are-stripped = {
    expr = scan [
      {
        name = "comment-only";
        code = stripComments "  x = 1; # this line mentions mkOption and nixpkgs but is a comment";
      }
    ];
    expected = [ ];
  };
}
