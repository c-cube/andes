
.PHONY: clean build build-dev all test

J?=3
OPTS= -j $(J) --profile=release

all: build test

build:
	@dune build $(OPTS)

clean:
	@dune clean

test-dune:
	@dune runtest $(OPTS)

TESTOPTS ?= -j 3
TESTTOOL=benchpress

test: build test-dune
	$(TESTTOOL) run -c examples/benchpress.sexp $(TESTOPTS) \
	  -t 30 --meta `git rev-parse HEAD` --progress -p andes examples/

WATCH_TARGET?=@all
watch:
	@dune build $(WATCH_TARGET) -w

