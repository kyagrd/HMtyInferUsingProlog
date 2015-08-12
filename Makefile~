main.pdf: main.aux main.tex intro.tex relwork.tex main.bbl
	pdflatex main

main.bbl: main.bib
	pdflatex main
	bibtex main
	pdflatex main
