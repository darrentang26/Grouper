.PHONY : all
all: toplevel

toplevel:
	cd src && ocamlbuild -use-ocamlfind -pkgs llvm,llvm.analysis -cflags -w,a toplevel.native

clean:
	cd src && ocamlbuild -clean
	rm *.out out hello
	rm tmp/*

sp_test: toplevel
	python3 scanner_parser_validation.py

hw_test: toplevel
	python3 hello_world_validation.py

e2e_test: toplevel
	python3 e2e_validation.py

tests: sp_test hw_test e2e_test

compile: toplevel
	src/toplevel.native -a $(in) > ast.out
	src/toplevel.native -s $(in) > sast.out
	src/toplevel.native -f $(in) > lifted.out
	src/toplevel.native -l $(in) > llvm.out
	src/toplevel.native -c $(in) | llc -relocation-model=pic | cc -o out -xassembler -

with_stdlib: toplevel
	python3 include_stdlib.py $(in)
	src/toplevel.native -a "tmp/tmpsrc.grp" > ast.out
	src/toplevel.native -s "tmp/tmpsrc.grp" > sast.out
	src/toplevel.native -f "tmp/tmpsrc.grp" > lifted.out
	src/toplevel.native -l "tmp/tmpsrc.grp" > llvm.out
	src/toplevel.native -c "tmp/tmpsrc.grp" | llc -relocation-model=pic | cc -o out -xassembler -

sanitize:
	_build/sanitize.sh