default:
	echo "Please specify which bundle to make: upload, linux, mac, windows"

linux:
	if [ `uname` != "Linux" ] ; \
	then \
		echo "This is not a Linux machine, is it?" ; \
	else \
		/bin/rm -rf alg-linux ; \
		mkdir -p alg-linux/theories ; \
		(cd .. ; make clean ; make native) ; \
		(cd ../doc; latexmk -c ; latexmk -view=none -pdf manual.tex) ; \
		/bin/cp ../alg.native alg-linux/alg ; \
		/bin/cp ../doc/manual.pdf alg-linux/manual.pdf ; \
		/bin/cp ../theories/*.th alg-linux/theories ; \
		zip -r alg-linux.zip alg-linux ; \
		/bin/rm -rf alg-linux ; \
		echo "Precompiled linux executable is now in alg-linux.zip" ; \
	fi

mac:
	if [ `uname` != "Darwin" ] ; \
	then \
		echo "This is not a MacOS machine, is it?" ; \
	else \
		/bin/rm -rf alg-macosx ; \
		mkdir -p alg-macosx/theories ; \
		(cd .. ; make clean ; make native) ; \
		(cd ../doc; latexmk -c ; latexmk -view=none -pdf manual.tex) ; \
		/bin/cp ../alg.native alg-macosx/alg ; \
		/bin/cp ../doc/manual.pdf alg-macosx/manual.pdf ; \
		/bin/cp ../theories/*.th alg-macosx/theories ; \
		zip -r alg-macosx.zip alg-macosx ; \
		/bin/rm -rf alg-macosx ; \
		echo "Precompiled MacOS X executable is now in alg-macosx.zip" ; \
	fi
