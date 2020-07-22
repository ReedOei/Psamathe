all: paper reuse-2020-talk

# Build twice to generate cross-refs.
# Not sure if there's a better way to do this.
paper: flow.tex
	pdflatex flow.tex
	pdflatex flow.tex

reuse-2020-talk: reuse-2020-talk.tex
	pdflatex reuse-2020-talk.tex
	pdflatex reuse-2020-talk.tex

