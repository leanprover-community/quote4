EXAMPLES = $(wildcard examples/*.lean)

.PHONY: all build examples

all: build examples

build:
	leanpkg build

examples: $(addsuffix .run, $(EXAMPLES))

examples/%.run: build
	LEAN_PATH=build lean examples/$*
