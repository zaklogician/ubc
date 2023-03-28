with import <nixpkgs> {};
let
  pythonEnv = python310.withPackages (ps: [
    ps.pytest
    ps.typing-extensions
    ps.mypy
    ps.autopep8
  ]);
in mkShell {
  packages = [
    pythonEnv
    pyright
    graphviz
    z3_4_11
    time
  ];
}
