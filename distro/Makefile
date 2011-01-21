OS=`uname`
VERSION=`date +%Y-%m-%d`

default:
	if [ $(OS) = "Linux" ] ; \
	then \
		make linux ; \
	elif [ $(OS) = "Darwin" ] ; \
	then \
		make mac ; \
	elif [ $(OS) = "CYGWIN_NT-6.1" ] ; \
	then \
		make windows ; \
	else \
		echo "Unknown operating system $(OS)." ; \
	fi

linux:
	if [ $(OS) != "Linux" ] ; \
	then \
		echo "This is not a Linux machine, is it?" ; \
	else \
		/bin/rm -rf alg-linux-* alg-*zip ; \
		mkdir -p alg-linux-$(VERSION)/theories ; \
		(cd .. ; make clean ; make default) ; \
		/bin/cp ../alg.native alg-linux-$(VERSION)/alg ; \
		/bin/cp ../doc/manual.pdf alg-linux-$(VERSION)/manual.pdf ; \
		/bin/cp ../theories/*.th alg-linux-$(VERSION)/theories ; \
		zip -r alg-linux-$(VERSION).zip alg-linux-$(VERSION) ; \
		/bin/rm -rf alg-linux ; \
		echo "Precompiled linux executable is now in alg-linux-$(VERSION).zip" ; \
		echo "Type \"make publish\" to publish it on the web." ; \
	fi

mac:
	if [ $(OS) != "Darwin" ] ; \
	then \
		echo "This is not a MacOS machine, is it?" ; \
	else \
		/bin/rm -rf alg-macosx-* alg-*.zip ; \
		mkdir -p alg-macosx-$(VERSION)/theories ; \
		(cd .. ; make clean ; make default) ; \
		/bin/cp ../alg.native alg-macosx-$(VERSION)/alg ; \
		/bin/cp ../doc/manual.pdf alg-macosx-$(VERSION)/manual.pdf ; \
		/bin/cp ../theories/*.th alg-macosx-$(VERSION)/theories ; \
		zip -r alg-macosx-$(VERSION).zip alg-macosx-$(VERSION) ; \
		/bin/rm -rf alg-macosx-$(VERSION) ; \
		echo "Precompiled MacOS X executable is now in alg-macosx-$(VERSION).zip" ; \
		echo "Type \"make publish\" to publish it on the web." ; \
	fi

windows:
	if [ $(OS) != "CYGWIN_NT-6.1" ] ; \
	then \
		echo "This is not a Windows machine, is it?" ; \
	else \
		/bin/rm -rf alg-windows alg-*.zip ; \
		mkdir -p alg-windows-$(VERSION)/theories ; \
		(cd .. ; make clean ; make native) ; \
		echo "Assuming the manual is compiled already." ; \
		/bin/cp ../alg.native alg-windows-$(VERSION)/alg ; \
		/bin/cp ../doc/manual.pdf alg-windows-$(VERSION)/manual.pdf ; \
		/bin/cp ../theories/*.th alg-windows-$(VERSION)/theories ; \
		zip -r alg-windows-$(VERSION).zip alg-windows-$(VERSION) ; \
		/bin/rm -rf alg-windows-$(VERSION) ; \
		echo "Precompiled Windows executable is now in alg-windows-$(VERSION)" ; \
		echo "You will have to zip and publish it yourself. Good luck."
	fi

publish:
	scp README.txt alg-*.zip math.andrej.com:/usr/local/var/math/wp-content/uploads/alg
