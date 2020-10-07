{
  description = "Readme of POPL20 artifact";

  outputs = { self, nixpkgs }: {

    inputs.nixpkgs.url = github:NixOS/nixpkgs/nixos-20.03;

    defaultPackage.x86_64-linux =
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation {
        name = "popl20-artifact-rouvoet";
        src = self;

        buildInputs = [
          (texlive.combine {
            inherit (texlive)
              scheme-small

              tufte-latex
              hardwrap
              catchfile
              titlesec
              palatino
              helvetic
              mathpazo

              marginfix
              epigraph

              fancyref
              nextpage
              booktabs

              acronym
              bigfoot # suffix.sty
              xstring

              # agda type setting
              polytable
              lazylist
              environ
              trimspaces
              newunicodechar
              catchfilebetweentags

              doublestroke # dsfont.sty

              biblatex
              ;
          })

          biber
          latexrun
        ];

        buildPhase = ''
          ulimit -n 1024
          latexrun readme.tex
        '';

        installPhase = "mkdir -p $out/; install index.pdf $out/readme.pdf";

        LANG   = "en_US.utf8";
        LC_ALL = "C";
      };
  };
}
