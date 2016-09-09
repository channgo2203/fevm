MODULES	:= common_definitions exceptions common_tactics DblibTactics LibTactics cstring monad monadinst nathelp tuplehelp update\
	 bitsrep bitsprops bitsops bitsopsprops cursor cursorprops pmap pmapprops reader writer\
	 mem storage stack instr program ere evm

VS	:= $(MODULES:%=%.v)

.PHONY:	coq clean

coq:	Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:	Makefile $(VS)
		coq_makefile -R . "" $(VS) -o Makefile.coq


clean:	Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	 
