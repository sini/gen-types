{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-identity.url = "github:sini/gen-identity";
    gen-algebra.url = "github:sini/gen-algebra";
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{ gen-harness, ... }:
    let
      prelude = inputs.gen-prelude.lib;
      genTypes = import ../lib {
        inherit prelude;
        identity = inputs.gen-identity.lib;
        algebra = inputs.gen-algebra.lib;
      };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-types";
      # `testModules` is the whole of `flake.tests`, which the batch asserter behind
      # `checks.default` forces unconditionally; cells asserting an ERROR live outside it, on
      # `flake.testsError` (`./tests-error.nix`), read by `nix-unit --flake ./ci#testsError`.
      testModules = ./tests;
      extraModules = [
        ./tests-error.nix
        ./tests-error-render.nix
        # The checked composites' old names are TOMBSTONES (lib/default.nix, `── THE RETIRED NAMES
        # ──`): `checks.root-surface` excludes them from the walk, and the generated
        # `root-surface-retired.test-retired-*` cells pin each exact message at the root seam, so a
        # resurrected or reworded tombstone reds.
        {
          gen.ci.rootSurface.retired = {
            listOf = "gen-types: `listOf` is renamed `checkedListOf`. A checker is a predicate over one value and gen-merge's `listOf` folds definitions across modules, so the two take two names (grammar R10 rule 3); the arguments and the behaviour are unchanged.";
            attrsOf = "gen-types: `attrsOf` is renamed `checkedAttrsOf`. A checker is a predicate over one value and gen-merge's `attrsOf` folds definitions across modules, so the two take two names (grammar R10 rule 3); the arguments and the behaviour are unchanged.";
            option = "gen-types: `option` is renamed `checkedOption`. A checker is a predicate over one value and gen-merge's `option` is an option type, so the two take two names (grammar R10 rule 3); the arguments and the behaviour are unchanged.";
          };
        }
      ];
      # `identity` reaches the suite because `tests/entry.nix` applies the STANDALONE root entry
      # with explicit arguments — which is what keeps that cell pure, since supplying both formals
      # means the shim's fetching defaults are never forced.
      specialArgs = {
        inherit genTypes prelude;
        identity = inputs.gen-identity.lib;
        algebra = inputs.gen-algebra.lib;
      };
    };
}
