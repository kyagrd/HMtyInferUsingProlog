main.pdf: main.bbl main.blg
	pdflatex main

main.bbl main.blg : main.aux main.bib
	bibtex main

main.aux: main.tex intro.tex relwork.tex
	pdflatex main
