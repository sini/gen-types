# gen-types REPL — all checkers in scope, aliased as t. Run: nix repl --impure --file ci/repl.nix
#
# The root declares only dependency formals, each defaulted from the root flake.lock, so it is
# called with exactly this entry's arguments: none under `nix repl --file`, where the root resolves
# its own pins, and the ci flake's own instances under `ci/tests/repl.nix`, which keeps that cell
# from fetching. `prelude` is the one the root wired, read through its `wire` seam rather than
# resolved a second time.
{ ... }@args:
let
  inherit (import ./.. (args // { wire = { deps, resolve }: deps; })) prelude;
  genTypes = import ./.. args;
in
{
  inherit prelude genTypes;
  t = genTypes;
}
// genTypes
