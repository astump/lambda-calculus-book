book.pdf:	book.tex definitions.tex book.idx book.ind Makefile \
		syntax.tex programming.tex confluence.tex stlc.tex introduction.tex
	rm -f book.aux
	pdflatex book
	makeindex book
	bibtex book
	pdflatex book
	pdflatex book
	cp book.pdf ..
	grep FIXME *.tex

book.idx: book.tex
	pdflatex book
	makeindex book

book.ind: book.tex
	makeindex book

clean:
	rm -f book.out *.aux *.ind *.bbl *.log  book.toc