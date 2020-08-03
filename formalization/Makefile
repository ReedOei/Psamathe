all: paper splash20-src

# Build a bunch of times to generate cross-refs.
# Is there'a better way to do this?
paper: flow.tex
	pdflatex flow.tex
	bibtex flow
	pdflatex flow.tex
	pdflatex flow.tex

splash20-src: splash20-src.tex
	pdflatex splash20-src.tex
	bibtex splash20-src
	pdflatex splash20-src.tex
	pdflatex splash20-src.tex

