
.PHONY: all
all: paper.pdf

LATEX_FLAGS := -interaction=nonstopmode
paper.pdf: paper.tex bibliography.bib
	-pdflatex $(LATEX_FLAGS) paper.tex 
	-biber paper
	pdflatex $(LATEX_FLAGS) paper.tex

.PHONY: clean
clean:
	rm -rf *.aux *.dvi *.log *~ *.toc *.pdf *.bfc *.bbl *.blg
