all: paper summer-2020-poster

# Build twice to generate cross-refs.
# Not sure if there's a better way to do this.
paper: flow.tex
	pdflatex flow.tex
	pdflatex flow.tex

summer-2020-poster: summer-2020-poster.tex
	pdflatex summer-2020-poster.tex
	pdflatex summer-2020-poster.tex

