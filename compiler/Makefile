# Builds with plain GHC — the compiler depends only on boot libraries
# (base, containers, mtl), so there is no package manager in the loop.
GHC ?= ghc
BUILD := build
SRC := src

.PHONY: all test clean

all: $(BUILD)/zkc

$(BUILD)/zkc: $(shell find $(SRC) -name '*.hs')
	@mkdir -p $(BUILD)
	$(GHC) -O1 -Wall -Wno-unused-imports -Wno-name-shadowing \
	  -i$(SRC) -outputdir $(BUILD)/objs -o $@ $(SRC)/Main.hs

$(BUILD)/spec: $(shell find $(SRC) test -name '*.hs')
	@mkdir -p $(BUILD)
	$(GHC) -O0 -i$(SRC) -itest -outputdir $(BUILD)/test-objs -o $@ test/Spec.hs

test: $(BUILD)/spec
	./$(BUILD)/spec

clean:
	rm -rf $(BUILD)