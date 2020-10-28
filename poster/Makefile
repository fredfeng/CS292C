TARGETS = muse.pdf

all: $(TARGETS)

%.pdf: %.tex Makefile
	pdflatex --enable-write18 $< &&	pdflatex $< && pdflatex $<

clean:
	  rm -f *.aux *.bbl *.blg *.log $(TARGETS)
