TARGET=alg
OCAMLBUILD=ocamlbuild -use-menhir

default: byte

byte:
	$(OCAMLBUILD) $(TARGET).byte
native:
	$(OCAMLBUILD) $(TARGET).native
profile:
	$(OCAMLBUILD) $(TARGET).p.native

conflicts:
	menhir --explain parser.mly
	rm parser.ml parser.mli

clean:
	$(OCAMLBUILD) -clean
	/bin/rm -f parser.conflicts
