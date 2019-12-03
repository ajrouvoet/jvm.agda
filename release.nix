let
  pkgs = import ./lib/nixos.nix { json = ./lib/nixos-19.09.json; };
  haskell = pkgs.haskell.packages.ghc881.override { overrides = self: super: {
    equivalence = super.callPackage ./lib/equivalence.nix {};
    regex-tdfa  = super.callPackage ./lib/regex-tdfa.nix {};
    regex-base  = super.callPackage ./lib/regex-base.nix {};
  }; };
in
  { agda = haskell.callPackage ./lib/agda.nix {}; }
