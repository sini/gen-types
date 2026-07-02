{
  inputs = {
    gen.url = "github:sini/gen";
    gen-prelude.url = "github:sini/gen-prelude";
    nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  };

  outputs =
    inputs@{ gen, ... }:
    let
      prelude = inputs.gen-prelude.lib;
      genTypes = import ../lib { inherit prelude; };
    in
    gen.lib.mkCi {
      inherit inputs;
      name = "gen-types";
      testModules = ./tests;
      specialArgs = { inherit genTypes prelude; };
    };
}
