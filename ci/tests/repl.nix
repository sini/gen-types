# The repl entry (`ci/repl.nix`, the harness `repl` command's file) loads, and loads exactly the
# library surface plus `prelude`, `genTypes` and `t`. Nothing else in the suite reaches that file,
# which is how it came to import `../lib` without the `identity` it requires (den-hoag-s34cm).
{
  genTypes,
  prelude,
  identity,
  ...
}:
{
  flake.tests.repl.test-entry-loads-the-surface = {
    expr = builtins.attrNames (import ../repl.nix { inherit prelude identity; });
    expected = builtins.attrNames (
      {
        inherit prelude genTypes;
        t = genTypes;
      }
      // genTypes
    );
  };
}
