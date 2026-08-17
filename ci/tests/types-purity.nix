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

  realSources = map (e: {
    inherit (e) name;
    code = stripComments (builtins.readFile e.path);
  }) (walk "lib/" typesDir);

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

  # A synthetic poisoned source — NOT written to disk, so the real scan stays green
  # while we prove the detector actually fires.
  poisoned = [
    {
      name = "injected";
      code = stripComments "  foo = lib.types.str; # comment mentioning nixpkgs is stripped";
    }
  ];
in
{
  # The real component source is clean.
  flake.tests.types-purity.test-library-source-is-dependency-free = {
    expr = scan realSources;
    expected = [ ];
  };

  # And that those labels carry their files' text. The cell above reports `[ ]` just as readily
  # for a read that returned one fixed string for every entry as for a library that is clean, and
  # it cannot tell those apart on its own: its expectation is an absence, and a scan of constants
  # produces nothing to find. So the reads are pinned here in the same shape the tree is pinned in
  # — an exact list, not a count — asked of a token that is genuinely present rather than
  # genuinely absent. Content is one axis of the subject; membership, which files are read at all,
  # is the other and is not asserted by this cell.
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

  # The scanner has teeth: an injected `lib.types` violation is caught.
  flake.tests.types-purity.test-detector-catches-injected-violation = {
    expr = scan poisoned != [ ];
    expected = true;
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
