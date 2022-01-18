ALLBENCHS=$(foreach x,o c s n g p a, $(foreach y,1 2 3, $(x)$(y))) as ct os cs

runbench: runbench.exe
	for b in $(ALLBENCHS); do ./runbench.exe $$b; done

MLFILES=benchmark.mli benchmark.ml runbench.ml

runbench.exe: $(MLFILES)
	ocamlopt -o runbench.exe $(MLFILES)

benchmark.ml: Benchmark.vo

clean::
	rm -f *.exe *.cm[iox] *.o
	rm -f benchmark.ml benchmark.mli
