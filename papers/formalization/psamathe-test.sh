#!/usr/bin/env bash

(
    cat header.tex
    ./psamathe.pl
    cat footer.tex
) > temp.tex

pdflatex temp.tex
xdg-open temp.pdf

