{ mkDerivation, base, containers, fail, mtl, QuickCheck, stdenv
, STMonadTrans, template-haskell, transformers, transformers-compat
}:
mkDerivation {
  pname = "equivalence";
  version = "0.3.5";
  sha256 = "17ab5a2a6759f6855de40acdd9dde0d0f89e9d9219a4bc8e52623816da97f698";
  libraryHaskellDepends = [
    base containers fail mtl STMonadTrans transformers
    transformers-compat
  ];
  testHaskellDepends = [
    base containers fail mtl QuickCheck STMonadTrans template-haskell
    transformers transformers-compat
  ];
  homepage = "https://github.com/pa-ba/equivalence";
  description = "Maintaining an equivalence relation implemented as union-find using STT";
  license = stdenv.lib.licenses.bsd3;
}
