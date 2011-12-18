default: doc native

native:
	cd src ; make native

byte:
	cd src ; make byte

doc:
	cd doc ; make

install:
	cd src ; make install