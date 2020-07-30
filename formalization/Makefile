all: paper

# Build twice to generate cross-refs.
# Not sure if there's a better way to do this.
paper: flow.tex
	pdflatex flow.tex
	bibtex flow
	pdflatex flow.tex
	pdflatex flow.tex

