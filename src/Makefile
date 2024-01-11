book.pdf:	book.tex definitions.tex book.idx Makefile \
		syntax.tex programming.tex confluence.tex stlc.tex
	rm -f book.aux
	pdflatex book
	makeindex book
	bibtex book
	pdflatex book
	pdflatex book
	cp book.pdf ..

book.idx: book.tex
	makeindex book
