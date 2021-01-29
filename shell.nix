{ pkgs ? import <nixpkgs> {} }:

with pkgs;
  mkShell {
    name = "agda-fragment";

    nativeBuildInputs = [
      git
      (agda.withPackages (p: [
        p.standard-library
      ]))
    ];
  }
