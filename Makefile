main.pdf: main.aux main.bbl main.tex intro.tex relwork.tex
	pdflatex main

main.aux: main.tex
	pdflatex main

main.bbl: main.aux main.bib
	bibtex main
	pdflatex main
