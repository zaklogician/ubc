{ pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/06278c77b5d162e62df170fec307e83f1812d94b.tar.gz") {}
}:

let
  pythonEnv = pkgs.python310.withPackages (ps: [
    ps.pytest
    ps.typing-extensions
    ps.mypy
    ps.autopep8
  ]);
in pkgs.mkShell {
  packages = [
    pythonEnv
    pkgs.pyright
    pkgs.graphviz
    pkgs.z3_4_11
    pkgs.time
  ];
}
