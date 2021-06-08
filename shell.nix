{ pkgs ? import <nixpkgs> {} }:

with pkgs;
  mkShell {
    name = "agda-fragment";

    nativeBuildInputs = [
      git
      coreutils
      (agda.withPackages (p: [
        p.standard-library
      ]))
    ];
  }
