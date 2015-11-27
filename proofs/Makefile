OCAMLBUILD= ocamlbuild -no-links -classic-display \
		-libs unix,nums,aez \
		-cflags "-I ../../lib/aez-0.3" \
		-lflags "-I ../../lib/aez-0.3" \
		-tags debug,annot

all: main
	cp _build/ex001_proof.byte ex001_proof
	
main: 
	$(OCAMLBUILD) ex001_proof.byte