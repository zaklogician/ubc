with import <nixpkgs> {};
let
  pythonEnv = python311.withPackages (ps: [
    ps.pytest
    ps.typing-extensions
    ps.mypy
  ]);
in mkShell {
  packages = [
    pythonEnv
    pyright
    graphviz
    z3_4_11
  ];
}
