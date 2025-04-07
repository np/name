# list ghc versions nix-env -f "<nixpkgs>" -qaP -A haskell.compiler
# nix develop .#ghc963
{
  inputs = {
   #nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
   #nixpkgs.url = "github:np/nixpkgs/45dfae0893d5d5bd0c74fb5cf6d9617829dd7597";
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.11";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    flake-root.url = "github:srid/flake-root";
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [
        inputs.haskell-flake.flakeModule
        inputs.flake-root.flakeModule
      ];
      perSystem = { self', system, lib, config, pkgs, ... }: {
        haskellProjects.ghc928 = {
          basePackages = pkgs.haskell.packages.ghc928;
        };
        haskellProjects.ghc963 = {
          basePackages = pkgs.haskell.packages.ghc963;
        };
        haskellProjects.default = {
          basePackages = pkgs.haskell.packages.ghc963; # works ...

          # https://github.com/srid/haskell-flake/blob/master/nix/modules/project/settings/all.nix
          settings = {
          };
          devShell = {
            tools = hp: { };
            #hlsCheck.enable = true;
          };
        };
        # haskell-flake doesn't set the default package, but you can do it here.
        packages.default = self'.packages.name;

      };
    };
}
