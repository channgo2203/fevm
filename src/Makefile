MODULES	:= common_definitions common_tactics DblibTactics LibTactics specific_tactics cstring monad monadinst nathelp tuplehelp listhelp update\
	 bitsrep bitsprops bitsops bitsopsprops cursor cursorprops pmap pmapprops reader writer\
	 mem storage stack instr program state ere evm

VS	:= $(MODULES:%=%.v)

.PHONY:	coq clean

coq:	Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:	Makefile $(VS)
		coq_makefile -R . "" $(VS) -o Makefile.coq


clean:	Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	 
