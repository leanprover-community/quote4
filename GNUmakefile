EXAMPLES = $(wildcard examples/*.lean)

.PHONY: all build examples

all: build examples

build:
	lake build

examples: $(addsuffix .run, $(EXAMPLES))

examples/%.run: build
	LEAN_PATH=build/lib lean examples/$*
