.PHONY: clean celan
COMPILE=ocamlfind opt -thread -syntax camlp5o -package ocanren,ocanren.syntax,mtime,mtime.clock.os -rectypes -linkpkg -g timeout.ml 

all:
	$(COMPILE) oc106.ml -o 106 
	$(COMPILE) ocanren_101.ml -o 101 

thtop:
	ocamlmktop -thread unix.cma threads.cma -o thtop

celan: clean
clean:
	rm *.cmx *.o timeout.cmi timeout.cmx -f
