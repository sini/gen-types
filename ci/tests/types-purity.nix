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
{ lib, ... }:
let
  typesDir = ../../lib;

  # Drop everything from the first `#` on each line (safe: `#` appears only in
  # comments across these files — no `#` in any string literal).
  stripComments =
    text:
    lib.concatStringsSep "\n" (
      map (line: lib.head (lib.splitString "#" line)) (lib.splitString "\n" text)
    );

  walk =
    dir:
    lib.concatLists (
      lib.mapAttrsToList (
        name: type:
        if type == "directory" then
          walk (dir + "/${name}")
        else if lib.hasSuffix ".nix" name then
          [ (dir + "/${name}") ]
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
      src: map (tok: "${src.name}: '${tok}'") (lib.filter (tok: lib.hasInfix tok src.code) forbidden)
    ) sources;

  realSources = map (p: {
    name = toString p;
    code = stripComments (builtins.readFile p);
  }) (walk typesDir);

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
