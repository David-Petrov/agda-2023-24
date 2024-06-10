{
  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    };
    flake-utils = {
      url = "github:numtide/flake-utils";
    };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    , ...
    } @ inputs : flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [];
        };
      in
      with pkgs; {
        devShell = mkShell {
          buildInputs = [
            ### Main

            (pkgs.agda.withPackages (ps: [
              ps.standard-library
            ]))
            pkgs.ghc
            pkgs.stack
          ];
        };
    });
}