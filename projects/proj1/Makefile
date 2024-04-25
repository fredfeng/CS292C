FILES := lib/desugar.ml lib/verify.ml lib/smt.ml benchmarks
ARCHIVE := submission.zip

all: build

build:
	dune build bin/main.exe

clean:
	dune clean
	rm -f $(ARCHIVE)

install: build
	dune install

$(ARCHIVE): $(FILES)
	zip -r $(ARCHIVE) $(FILES)

zip: $(ARCHIVE)


.PHONY: all build clean install