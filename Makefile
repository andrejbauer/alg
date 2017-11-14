INSTALL_DIR ?= /usr/local/bin

LATEXMK ?= latexmk
LATEXMK_FLAGS ?= -pdf -cd

OCAMLBUILD ?= ocamlbuild -use-menhir
OCAMLBUILD_FLAGS ?= -j 4 -use-menhir -menhir "menhir --explain"

default: doc/manual.pdf alg.native

.PHONY: alg.native alg.bytes alg.d.bytes alg.p.native

alg.native alg.bytes alg.d.bytes alg.p.native: src/version.ml
	$(OCAMLBUILD) $(OCAMLBUILD_FLAGS) $@

doc/manual.pdf: doc/manual.tex
	$(LATEXMK) $(LATEXMK_FLAGS) doc/manual.tex

src/version.ml:
	export VERSION=`@git describe --always --long` ; \
	export OS=`uname` ; \
	export DATE=`date +%Y-%m-%d` ; \
	echo "let version = \"$$VERSION\" ;; let os = \"$$OS\" ;; let date = \"$$DATE\"" > src/version.ml

clean:
	$(OCAMLBUILD) -clean
	$(LATEXMK) -C -cd doc/manual.tex

install:
	cd src ; make install
