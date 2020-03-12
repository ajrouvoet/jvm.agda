{ mkDerivation, fetchFromGitHub, aeson, alex, array, async, base, binary, blaze-html
, boxes, bytestring, Cabal, containers, data-hash, deepseq
, directory, edit-distance, emacs, equivalence, exceptions
, filemanip, filepath, geniplate-mirror, gitrev, happy, hashable
, hashtables, haskeline, ieee754, mtl, murmur-hash, pretty, process
, process-extras, QuickCheck, regex-tdfa, split, stdenv, stm
, strict, tasty, tasty-hunit, tasty-quickcheck, tasty-silver
, template-haskell, temporary, text, time, transformers
, unix-compat, unordered-containers, uri-encode, zlib
}:
mkDerivation {
  pname = "Agda";
  version = "42.0.0";

  src = fetchFromGitHub {
    owner  = "agda";
    repo   = "agda";
    rev    = "99b858c75cbd73ae3a60491f4dcabadb5cf9cc6f";
    sha256 = "09sk96877vws9hs4849bgrgrngw4a30c62a9vji43yhc8dfad31y";
  };

  isLibrary = true;
  isExecutable = true;
  enableSeparateDataOutput = true;
  setupHaskellDepends = [ base Cabal directory filepath process ];
  libraryHaskellDepends = [
    aeson array async base binary blaze-html boxes bytestring
    containers data-hash deepseq directory edit-distance equivalence
    exceptions filepath geniplate-mirror gitrev hashable hashtables
    haskeline ieee754 mtl murmur-hash pretty process regex-tdfa split
    stm strict template-haskell text time transformers
    unordered-containers uri-encode zlib
  ];
  libraryToolDepends = [ alex happy ];
  executableHaskellDepends = [ base directory filepath process ];
  executableToolDepends = [ emacs ];
  testHaskellDepends = [
    array base bytestring containers directory filemanip filepath mtl
    process process-extras QuickCheck regex-tdfa tasty tasty-hunit
    tasty-quickcheck tasty-silver temporary text unix-compat uri-encode
  ];
  doCheck = false;
  postInstall = ''
    files=("$data/share/ghc-"*"/"*"-ghc-"*"/Agda-"*"/lib/prim/Agda/"{Primitive.agda,Builtin"/"*.agda})
    for f in "''${files[@]}" ; do
      $out/bin/agda $f
    done
    for f in "''${files[@]}" ; do
      $out/bin/agda -c --no-main $f
    done
    $out/bin/agda-mode compile
  '';
  homepage = "http://wiki.portal.chalmers.se/agda/";
  description = "A dependently typed functional programming language and proof assistant";
  license = "unknown";
}
