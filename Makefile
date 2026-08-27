comp: CoqMakefile 
	make -f CoqMakefile 


CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

cleanaux:
	rm theories/.*.aux  theories/syntax/.*.aux 

clean: 
	make clean -f CoqMakefile 

