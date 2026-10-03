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
    # The intensional plane's one owner (grammar R10 rule 1): a type's per-component identity is
    # built on its `componentsPreimage` and decided by its `sealedCollisionEq`. gen-algebra sits in
    # the substrate stratum and declares no inputs, so the edge points down and closes no cycle.
    gen-algebra.url = "github:sini/gen-algebra";
  };

  outputs =
    {
      gen-prelude,
      gen-identity,
      gen-algebra,
      ...
    }:
    {
      lib = import ./. {
        prelude = gen-prelude.lib;
        identity = gen-identity.lib;
        algebra = gen-algebra.lib;
      };
    };
}
