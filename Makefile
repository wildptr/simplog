.PHONY: all FORCE

all: slc.native

%.native: FORCE
	ocamlbuild -use-ocamlfind -use-menhir -package zarith -package extlib -package ocamlgraph $*.native
