all: paper

# Build a bunch of times to generate cross-refs.
# Is there'a better way to do this?
paper: flow.tex
	pdflatex flow.tex
	bibtex flow
	pdflatex flow.tex
	pdflatex flow.tex

