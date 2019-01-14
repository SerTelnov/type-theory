.PHONY: pack all run clean

PARSER_PATH=src/parser/
NORMZ_PATH=src/normalization/
#OUT_PATH=out/$(TARGET)/

GENERATED=$(PARSER_PATH)parser.mli $(PARSER_PATH)parser.ml $(PARSER_PATH)lexer.ml
OCAMLC=ocamlc # ocamlopt for speed
PACKAGE=hw.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run: main.exe
	./main.exe

$(PARSER_PATH)tree.cmi:
	cd $(PARSER_PATH) && $(OCAMLC) -c tree.ml

# hw1
# main.exe: $(GENERATED) $(PARSER_PATH)tree.cmi
# 	cd $(PARSER_PATH) && $(OCAMLC) tree.ml $(GENERATED:src/parser/%=%) main.ml -o ../../main.exe

# hw2
main.exe: $(GENERATED) $(PARSER_PATH)tree.cmi
	cd $(PARSER_PATH) && $(OCAMLC) tree.ml $(GENERATED:src/parser/%=%) ../normalization/main.ml -o ../../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src

$(GENERATED): $(PARSER_PATH)lexer.mll $(PARSER_PATH)parser.mly
	ocamllex $(PARSER_PATH)lexer.mll 
	ocamlyacc $(PARSER_PATH)parser.mly

clean:
	cd $(PARSER_PATH) && $(DEL) $(GENERATED:src/parser/%=%) *.c* *.o*
	cd $(NORMZ_PATH) && $(DEL) $(GENERATED:src/parser/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)