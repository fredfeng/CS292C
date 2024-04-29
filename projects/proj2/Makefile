FILES := lib/solver/bcp.ml lib/solver/dpll.ml lib/solver/cdcl.ml
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