.PHONY: all FORCE

all: Simplog_Parser_Test.native

%.native: FORCE
	ocamlbuild -use-ocamlfind -use-menhir -package zarith -package extlib $*.native
