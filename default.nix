# Standalone (non-flake) entry. Flake consumers should use the `.lib` output.
#
# gen-types is a function of two named values — gen-prelude (the pure utility base) and
# gen-identity (the substrate's one minting authority, a dependency-free leaf). Defaults fetch the
# flake-locked revs (content-addressed via narHash, so the plain-import path stays pure and in
# lockstep with the flake output). Pass either explicitly to override, e.g. a local checkout.
#
# ★ WHY IT IS BOTH DEFAULTS AND NOT ONE, RECORDED BECAUSE THE OMISSION WAS SILENT.
# `lib/default.nix` takes `{ prelude, identity }`, and this shim supplied only `prelude` — so
# `import ./.` was a lambda whose application threw `called without required argument 'identity'`
# while the flake output was perfectly fine. The comment above it already promised lockstep with
# the flake, which is exactly the drift this file exists to prevent: **a shim naming fewer
# arguments than the library it delegates to is not a lockstep entry — it is a second signature
# that nothing compares against the first.**
#
# ★★ THE DEFAULTS ARE READ THROUGH `root.inputs`, BY LABEL, NEVER BY NODE-KEY SPELLING, and that is
# not a stylistic preference. A lock's node KEY is a disambiguated name: a second instance of a
# library becomes `gen-prelude_2`, and which key the ROOT's own input got is not something a reader
# can infer from the spelling. `lock.nodes.root.inputs.<label>` is the edge the root actually
# resolves; indexing `lock.nodes.<label>` reads whatever node happens to hold that key, which on a
# lock carrying two instances is the wrong one and is silent about being wrong.
{
  lock ? builtins.fromJSON (builtins.readFile ./flake.lock),
  fetch ? name: builtins.fetchTree lock.nodes.${lock.nodes.root.inputs.${name}}.locked,
  prelude ? import "${fetch "gen-prelude"}/lib",
  # A dependency-free leaf, so its lib is a bare value and this takes no argument. Derived from
  # THIS shim's lock so the whole construction mints through one encoding — two instances would be
  # two content-address formulas for one node.
  identity ? import "${fetch "gen-identity"}/lib",
}:
import ./lib { inherit prelude identity; }
