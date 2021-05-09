PKG = Qq

include lean.mk

EXAMPLES = $(wildcard examples/*.lean)

.PHONY: examples

examples: $(addsuffix .run, $(EXAMPLES))

examples/%.run: $(OBJS)
	lean examples/$*
