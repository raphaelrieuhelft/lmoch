OCAMLBUILD= ocamlbuild -no-links -classic-display \
		-libs unix,nums,aez \
		-cflags "-I ../../lib/aez-0.3" \
		-lflags "-I ../../lib/aez-0.3" \
		-tags debug,annot

NAME = ex012_check2_proof
all: main
	cp _build/$(NAME).byte $(NAME)
	
main: 
	$(OCAMLBUILD) $(NAME).byte