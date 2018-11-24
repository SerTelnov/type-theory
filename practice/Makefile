.PHONY: pack all run clean

TARGET=parser

SRC_PATH=src/$(TARGET)/
#OUT_PATH=out/$(TARGET)/

GENERATED=$(SRC_PATH)parser.mli $(SRC_PATH)parser.ml $(SRC_PATH)lexer.ml
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

$(SRC_PATH)tree.cmi:
	cd $(SRC_PATH) && $(OCAMLC) -c tree.ml

main.exe: $(GENERATED) $(SRC_PATH)tree.cmi
	cd $(SRC_PATH) && $(OCAMLC) tree.ml $(GENERATED:src/parser/%=%) main.ml -o ../../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src

$(GENERATED): $(SRC_PATH)lexer.mll $(SRC_PATH)parser.mly
	ocamllex $(SRC_PATH)lexer.mll 
	ocamlyacc $(SRC_PATH)parser.mly

clean:
	cd $(SRC_PATH) && $(DEL) $(GENERATED:src/parser/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)