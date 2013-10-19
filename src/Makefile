INSTALL_DIR=/usr/local/bin
TARGET=alg
OCAMLBUILD=ocamlbuild -use-menhir

default: native nomenhir

.PHONY: version.ml nomenhir

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
	export VERSION=`git describe --always --long` ; \
	export OS=`uname` ; \
	export DATE=`date +%Y-%m-%d` ; \
	echo "let version = \"$$VERSION\" ;; let os = \"$$OS\" ;; let date = \"$$DATE\"" > version.ml

nomenhir: native
	/bin/cp -f _build/parser.ml nomenhir
	/bin/cp -f _build/lexer.ml nomenhir
