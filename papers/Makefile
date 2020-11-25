all: paper splash20-src reuse20-poster

# Build a bunch of times to generate cross-refs.
# Is there'a better way to do this?
paper: flow.tex
	pdflatex flow.tex
	bibtex flow
	pdflatex flow.tex
	pdflatex flow.tex
	xdg-open flow.pdf

splash20-src: splash20-src.tex
	pdflatex splash20-src.tex
	bibtex splash20-src
	pdflatex splash20-src.tex
	pdflatex splash20-src.tex
	xdg-open splash20-src.pdf

padl-21: padl-21.tex
	pdflatex padl-21.tex
	bibtex padl-21
	pdflatex padl-21.tex
	pdflatex padl-21.tex
	xdg-open padl-21.pdf

padl-21-extended: padl-21-extended.tex
	pdflatex padl-21-extended.tex
	bibtex padl-21-extended
	pdflatex padl-21-extended.tex
	pdflatex padl-21-extended.tex
	xdg-open padl-21-extended.pdf

reuse20-poster: reuse20-poster/poster.tex
	( cd reuse20-poster && make )

clean:
	rm -f *.aux *.bbl *.blg *.out *.nav *.snm *.toc *.vrb ":w"

