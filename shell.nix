{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs;
stdenv.mkDerivation {
  name = "futhark-ad";
  buildInputs = [ zlib zlib.out pkgconfig haskell.compiler.ghc883 cabal-install hlint (python38.withPackages(ps: with ps; [ numpy toolz ]))];
}
