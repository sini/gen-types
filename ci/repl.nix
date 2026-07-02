# gen-types REPL — all checkers in scope, aliased as t.
let
  prelude = (builtins.getFlake "github:sini/gen-prelude").lib;
  genTypes = import ../lib { inherit prelude; };
in
{
  inherit prelude genTypes;
  t = genTypes;
}
// genTypes
