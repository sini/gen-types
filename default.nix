# Standalone (non-flake) entry. gen-types has a single dependency (gen-prelude),
# so this is a FUNCTION of that named value — with a default that fetches the
# flake-locked gen-prelude, keeping the plain-import path in lockstep with the
# flake output (per the gen root-file convention).
{
  prelude ?
    let
      lock = builtins.fromJSON (builtins.readFile ./flake.lock);
    in
    import "${builtins.fetchTree lock.nodes.gen-prelude.locked}/lib",
}:
import ./lib { inherit prelude; }
