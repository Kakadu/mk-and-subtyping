.PHONY: clean celan

all:
	ocamlfind opt -thread -syntax camlp5o -package ocanren,ocanren.syntax,mtime,mtime.clock.os -rectypes timeout.ml oc106.ml -o 106 -linkpkg

thtop:
	ocamlmktop -thread unix.cma threads.cma -o thtop

celan: clean
clean:
	rm *.cmx *.o timeout.cmi timeout.cmx -f
