INSTALL_DIR=/usr/local/bin
TARGET=alg
OCAMLBUILD=ocamlbuild -use-menhir

default: native

byte:
	$(OCAMLBUILD) $(TARGET).byte
native:
	$(OCAMLBUILD) $(TARGET).native
profile:
	$(OCAMLBUILD) $(TARGET).p.native
debug:
	$(OCAMLBUILD) -cflags -g $(TARGET).native

conflicts:
	menhir --explain parser.mly
	rm parser.ml parser.mli

install: native
	/bin/cp -i _build/alg.native $(INSTALL_DIR)/alg

clean:
	$(OCAMLBUILD) -clean
	/bin/rm -f parser.conflicts
