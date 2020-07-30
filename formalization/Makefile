all: paper

# Build twice to generate cross-refs.
# Not sure if there's a better way to do this.
paper: flow.tex
	xelatex flow.tex
	bibtex flow
	xelatex flow.tex
	xelatex flow.tex

