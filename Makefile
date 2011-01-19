INSTALL_DIR=/usr/local/bin
TARGET=alg
OCAMLBUILD=ocamlbuild -use-menhir

default: native

.PHONY: version.ml

byte:	version.ml
	$(OCAMLBUILD) $(TARGET).byte
native: version.ml
	$(OCAMLBUILD) $(TARGET).native
profile: version.ml
	$(OCAMLBUILD) $(TARGET).p.native
debug: version.ml
	$(OCAMLBUILD) -cflags -g -lflags -g $(TARGET).native
debug-byte: version.ml
	$(OCAMLBUILD) -cflags -g -lflags -g $(TARGET).byte

conflicts:
	menhir --explain parser.mly
	rm parser.ml parser.mli

install: native
	/bin/cp -i _build/alg.native $(INSTALL_DIR)/alg

clean:
	$(OCAMLBUILD) -clean
	/bin/rm -f parser.conflicts

version.ml:
	export VERSION=`hg id --id` ; \
	export OS=`uname` ; \
	echo "let version = \"$$VERSION\" ;; let os = \"$$OS\" ;;" > version.ml
