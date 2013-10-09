PDFLATEX=pdflatex

default: manual.pdf

manual.pdf: manual.tex
	$(PDFLATEX) manual.tex
	$(PDFLATEX) manual.tex
clean:
	/bin/rm -f *.{aux,log,toc,mtc} *.mtc?
