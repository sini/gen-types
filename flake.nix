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
      # `nix flake check` forces the WHNF of every top-level output and nothing deeper, so this root's
      # green quantified over the `lib` SPINE alone: a member of the published surface could throw and
      # the check still exited 0 (measured — den-hoag-z1ta6). Hanging the force on that spine is what
      # makes the green mean "the surface evaluates", and a library needs no new output name for it.
      # The depth is each member's WHNF and no deeper: a retirement tombstone is a published `throw`
      # by design (gen-scope's `buildNodes`), so a deep force is red on a healthy tree.
      lib =
        let
          surface = import ./. {
            prelude = gen-prelude.lib;
            identity = gen-identity.lib;
          };
        in
        builtins.deepSeq (builtins.mapAttrs (_: builtins.typeOf) surface) surface;
    };
}
