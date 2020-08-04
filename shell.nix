{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs;
stdenv.mkDerivation {
  name = "futhark-ad";
  buildInputs = [ zlib zlib.out pkgconfig haskell.compiler.ghc883 ];
}
