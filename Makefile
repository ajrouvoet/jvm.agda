BUILDDIR = _build
TARGET   = typed-compilation
BUILD    = $(BUILDDIR)/$(TARGET)
OUT      = $(BUILDDIR)/bin
EXES     = ./src/CF/Examples/
SRC     := $(wildcard src/*)

all:
	agda -v 2 src/Everything.agda

build/typed-compilation.tar.gz: doc
	rm -rf $(BUILD) && mkdir -p $(BUILD)
	cp -r README.md src/ lib/ doc/ .agda-lib Makefile $(BUILD)
	find $(BUILD) -iname *.agdai -exec rm {} \;
	cd $(BUILDDIR) && tar cvzf $(TARGET).tar.gz --numeric-owner $(TARGET)

build: build/typed-compilation.tar.gz

$(OUT)/%: $(EXES)/%.agda $(SRC)
	stack exec --package ieee754 --package text agda -- --compile-dir $(OUT) --compile $<

examples: $(OUT)/Ex1 $(OUT)/Ex2 

doc: src/
	rm -rf doc
	mkdir doc
	agda --html --html-dir=doc src/Everything.agda
