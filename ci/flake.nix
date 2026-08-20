{
  inputs = {
    gen-harness.url = "github:sini/gen-harness";
    gen-prelude.url = "github:sini/gen-prelude";
    gen-identity.url = "github:sini/gen-identity";
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{ gen-harness, ... }:
    let
      prelude = inputs.gen-prelude.lib;
      genTypes = import ../lib {
        inherit prelude;
        identity = inputs.gen-identity.lib;
      };
    in
    gen-harness.lib.mkCi {
      inherit inputs;
      name = "gen-types";
      testModules = ./tests;
      # `identity` reaches the suite because `tests/entry.nix` applies the STANDALONE root entry
      # with explicit arguments — which is what keeps that cell pure, since supplying both formals
      # means the shim's fetching defaults are never forced.
      specialArgs = {
        inherit genTypes prelude;
        identity = inputs.gen-identity.lib;
      };
    };
}
