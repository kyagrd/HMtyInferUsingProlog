main.pdf: main.bbl main.blg
	pdflatex main

main.bbl main.blg : main.aux main.bib
	bibtex main

main.aux: main.tex intro.tex relwork.tex
	pdflatex main

CAMSRC=main.bib main.tex intro.tex relwork.tex Makefile \
       llncs.cls splncs03.bst sprmindx.sty remreset.sty aliascnt.sty

camreadyAhnVezzosi.zip: $(CAMSRC) Makefile
	zip $@ $(CAMSRC)
