all: build

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

clean:
	$(MAKE) --no-print-directory -f CoqMakefile clean
	$(MAKE) -C benchmark clean
	rm -f CoqMakefile CoqMakefile.conf

build: CoqMakefile
	@$(MAKE) --no-print-directory -f CoqMakefile

coqbench:
	coqtop -R . Tries -R mmaps MMaps -batch -load-vernac-source benchmark/Runbench.v

ocamlbench:
	@$(MAKE) --no-print-directory -C benchmark

documentation:
	coq2html -base Tries -no-css -d docs *.glob *.v
