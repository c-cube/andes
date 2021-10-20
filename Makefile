
.PHONY: clean build build-dev all test

J?=3
OPTS= -j $(J) --profile=release

all: build test

build:
	@dune build $(OPTS)

build-release:
	@dune build $(OPTS) -p andes

clean:
	dune clean

test:
	dune runtest

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

WATCH_TARGET?=@all
watch:
	@dune build $(WATCH_TARGET) -w

