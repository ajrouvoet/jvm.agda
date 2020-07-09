BUILDDIR = _build
TARGET   = jvm.agda
BUILD    = $(BUILDDIR)/$(TARGET)
OUT      = $(BUILDDIR)/bin
EXES     = ./src/CF/Examples/
SRC     := $(wildcard src/*)

build/sessions.agda.tar.gz:
	rm -rf $(BUILD) && mkdir -p $(BUILD)
	cp -r README.agda src/ lib/ $(BUILD)
	find $(BUILD) -iname *.agdai -exec rm {} \;
	cd $(BUILDDIR) && tar cvzf $(TARGET).tar.gz --numeric-owner $(TARGET)

$(OUT)/%: $(EXES)/%.agda $(SRC)
	stack exec --package ieee754 --package text agda -- --compile-dir $(OUT) --compile $<

examples: $(OUT)/Ex1 $(OUT)/Ex2 

doc: src/
	rm -rf doc
	mkdir doc
	agda --html --html-dir=doc src/Everything.agda
