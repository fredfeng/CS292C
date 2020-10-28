# ---------------------------------------------------------
# type "make" command in Unix to create the PDF file 
# ---------------------------------------------------------

PDF_VIEWER?=open -a Preview 

# Main filename
FILE= main

# ---------------------------------------------------------

all:
	pdflatex  ${FILE}
	pdflatex  ${FILE}
	bibtex ${FILE}
	bibtex ${FILE}
	bibtex ${FILE}
	pdflatex  ${FILE}
	pdflatex  ${FILE}

quick:
	pdflatex ${FILE}

clean:
	(rm -rf *.aux *.bbl *.blg *.glg *.glo *.gls *.ilg *.ist *.lof *.log *.lot *.nlo *.nls *.out *.toc *.fdb_latexmk *.bbl)

veryclean:
	make clean
	rm -f *~ *.*%
	rm -f $(FILE).pdf $(FILE).ps

mk: 
	@latexmk -pdf -c-style-errors $(FILE)
allclean: 
	@latexmk -C -pdf $(FILE)
v: mk
	$(PDF_VIEWER) $(FILE).pdf &
