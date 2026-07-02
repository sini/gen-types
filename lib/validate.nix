# Validator base, folded in from lib/validate.nix (which used nixpkgs `lib.*` list
# combinators). Re-expressed against gen-prelude so it stays inside the purity
# boundary. A validator is a named predicate contract over a kind's instances:
# a plain record { name; pred; message; } evaluated against every instance, with
# failures collected into an Either — { right = instances; } | { left = [failure]; }.
#
# Scope note: this is the validator BASE only (mkValidator/runValidators/
# formatErrors/defaultOnError). The field-aware wrappers and the kind-driven
# `validateInstances` entry point stay in the registry lib — they reach into
# gen-schema kind values, not the pure checker surface.
{ prelude }:
let
  inherit (prelude)
    concatLists
    concatMap
    concatMapStringsSep
    mapAttrsToList
    ;

  mkValidator = name: pred: message: {
    inherit name pred message;
  };

  runValidators =
    kind: validators: instances:
    let
      failures = concatLists (
        mapAttrsToList (
          name: instance:
          concatMap (
            v:
            if v.pred instance then
              [ ]
            else
              [
                {
                  inherit kind name;
                  validator = v.name;
                  inherit (v) message;
                }
              ]
          ) validators
        ) instances
      );
    in
    if failures == [ ] then { right = instances; } else { left = failures; };

  formatErrors =
    failures:
    concatMapStringsSep "\n" (f: "  ${f.kind} '${f.name}': ${f.validator} — ${f.message}") failures;

  defaultOnError =
    left:
    if builtins.isList left then
      throw "gen-types validation failed:\n${formatErrors left}"
    else
      throw "gen-types: unexpected validation error: ${builtins.toJSON left}";
in
{
  inherit
    mkValidator
    runValidators
    formatErrors
    defaultOnError
    ;
}
