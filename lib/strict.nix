# Closed-world / unknown-key rejection, folded in from lib/strict.nix.
#
# The old mkStrictModule expressed "reject any key not declared" as a module-system
# device: it set `_module.freeformType` to a `lib.mkOptionType` whose merge always
# threw. That is the merge half's job. The pure CHECKING half of the same intent is
# just: given the set of declared keys, a value is strict iff it carries no others.
#
# Two forms, both nixpkgs-lib-free:
#   strict knownNames           — a standalone checker rejecting undeclared keys
#   struct(...).override { unknown = false; }  — the same discipline inside a struct
{ prelude }:
let
  inherit (prelude)
    attrNames
    concatStringsSep
    isAttrs
    map
    ;
  joinKeys = list: concatStringsSep ", " (map (e: "'${e}'") list);
in
{
  # strict : [str] -> checker
  # Takes the identity core's `mkChecker` (name/verify/check/__name/__id/__mint).
  #
  # ★ EVERY STRICT TYPE IS NAMED "strict", so the name distinguishes NONE of them — `strict [ "a" ]`
  # and `strict [ "b" ]` compared EQUAL under a name-only identity, measured. The declared key set
  # is the whole of the distinguishing content and it is a list of strings, so it enters the mint
  # and this family is structural outright.
  strict =
    mkChecker: knownNames:
    mkChecker "strict" knownNames "strict" (
      v:
      if !isAttrs v then
        "expected an attribute set for strict-key checking, got ${builtins.typeOf v}"
      else
        let
          extra = attrNames (builtins.removeAttrs v knownNames);
        in
        if extra == [ ] then
          null
        else
          "keys [${joinKeys extra}] are unrecognized, expected keys are [${joinKeys knownNames}]"
    );
}
