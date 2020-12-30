{ pkgs ? import <nixpkgs> {} }:

with pkgs;
  mkShell {
    name = "agda-fragment";

    nativeBuildInputs = [
      (agda.withPackages (p: [
        p.standard-library
      ]))
    ];
  }
