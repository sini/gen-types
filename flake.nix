{
  description = "gen-types: pure, nixpkgs-lib-free structural type checker for the gen ecosystem";

  # A LEAF library: the single dependency is gen-prelude (itself dependency-free).
  # gen-types sits BELOW gen-schema — the byte-mode merge engine verifies leaves with
  # these checkers, and gen-schema's registry sits on top of the merge engine. Keeping
  # gen-types a standalone leaf breaks the otherwise-cyclic flake dependency.
  # The test runner lives in ./ci, a separate flake.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
    # The substrate's one minting authority (ADR-0016 ruling 5), a dependency-free leaf. gen-types
    # is a LEAF too and could never have reached the mint while it lived in gen-schema — that
    # cycle is the whole reason the authority became a library of its own.
    gen-identity.url = "github:sini/gen-identity";
  };

  outputs =
    { gen-prelude, gen-identity, ... }:
    {
      lib = import ./lib {
        prelude = gen-prelude.lib;
        identity = gen-identity.lib;
      };
    };
}
