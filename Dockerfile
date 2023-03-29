FROM nixos/nix:2.13.3
WORKDIR /ubc
COPY . /ubc
RUN ["nix-shell", "shell.nix"]
