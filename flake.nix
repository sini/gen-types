{
  description = "gen-types: pure, nixpkgs-lib-free structural type checker for the gen ecosystem";

  # A LEAF library: the single dependency is gen-prelude (itself dependency-free).
  # gen-types sits BELOW gen-schema — the byte-mode merge engine verifies leaves with
  # these checkers, and gen-schema's registry sits on top of the merge engine. Keeping
  # gen-types a standalone leaf breaks the otherwise-cyclic flake dependency.
  # The test runner lives in ./ci, a separate flake.
  inputs = {
    gen-prelude.url = "github:sini/gen-prelude";
  };

  outputs =
    { gen-prelude, ... }:
    {
      lib = import ./lib { prelude = gen-prelude.lib; };
    };
}
