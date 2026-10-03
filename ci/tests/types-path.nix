# gen-types: `path` admits exactly what nixpkgs' `types.path` admits, and `pathLike` exactly what
# `types.pathWith { }` admits (den-hoag-fyx6m). Both are `lib.isStringLike`: a string, a path, or a
# set `toString` coerces (a derivation, an `outPath` set, a `__toString` set); `path` adds that the
# value is absolute, a derivation counting as absolute. The reference is this flake's root nixpkgs
# node, not flake-parts' `lib`, whose older `pathWith` lacks the derivation clause. RED under
# `isPath`: every string-like row but the path literal refuses.
{
  genTypes,
  inputs,
  ...
}:
let
  t = genTypes;
  np = inputs.nixpkgs.lib.types;
  file = builtins.toFile "fyx6m" "";
  battery = {
    absoluteString = "/etc/x";
    relativeString = "etc/x";
    dotRelativeString = "./x";
    emptyString = "";
    pathLiteral = ./.;
    storePathString = builtins.unsafeDiscardStringContext file;
    contextString = file;
    contextRelativeString = builtins.substring 1 100 file;
    derivation = derivation {
      name = "fyx6m";
      builder = "/bin/sh";
      system = "x86_64-linux";
    };
    derivationRelativeOutPath = {
      type = "derivation";
      outPath = "x";
    };
    derivationNoOutPath = {
      type = "derivation";
    };
    outPathAbsolute = {
      outPath = "/etc/x";
    };
    outPathRelative = {
      outPath = "x";
    };
    toStringAbsolute = {
      __toString = _: "/etc/x";
    };
    toStringRelative = {
      __toString = _: "x";
    };
    attrs = { };
    int = 1;
    null = null;
    list = [ ];
  };
  disagree =
    gen: ref:
    builtins.filter (n: (gen.verify battery.${n} == null) != ref.check battery.${n}) (
      builtins.attrNames battery
    );
in
{
  flake.tests.types-path.test-path-absolute-string-ok = {
    expr = t.path.verify "/etc/x";
    expected = null;
  };
  flake.tests.types-path.test-path-derivation-ok = {
    expr = t.path.verify battery.derivation;
    expected = null;
  };
  flake.tests.types-path.test-path-toString-absolute-ok = {
    expr = t.path.verify battery.toStringAbsolute;
    expected = null;
  };
  flake.tests.types-path.test-path-relative-string-fail = {
    expr = t.path.verify "etc/x";
    expected = "expected type 'path' but value \"etc/x\" is of type 'string'";
  };
  flake.tests.types-path.test-pathLike-toString-relative-ok = {
    expr = t.pathLike.verify battery.toStringRelative;
    expected = null;
  };
  flake.tests.types-path.test-pathLike-derivation-without-outPath-fail = {
    expr = t.pathLike.verify battery.derivationNoOutPath;
    expected = "expected type 'pathLike' but value { type = …; } is of type 'set'";
  };
  # the differentials: no battery value on which gen and nixpkgs disagree
  flake.tests.types-path.test-path-agrees-with-types-path = {
    expr = disagree t.path np.path;
    expected = [ ];
  };
  flake.tests.types-path.test-pathLike-agrees-with-pathWith = {
    expr = disagree t.pathLike (np.pathWith { });
    expected = [ ];
  };
  # control: the battery straddles the reference, and the reference carries the derivation clause
  # (`derivationRelativeOutPath` admitted), so neither differential passes on a collapsed or older body
  flake.tests.types-path.test-control-battery-straddles = {
    expr = builtins.filter (n: np.path.check battery.${n}) (builtins.attrNames battery);
    expected = [
      "absoluteString"
      "contextString"
      "derivation"
      "derivationRelativeOutPath"
      "outPathAbsolute"
      "pathLiteral"
      "storePathString"
      "toStringAbsolute"
    ];
  };
}
