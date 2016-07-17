CORES := -j
STLC := .
SRCS := $(wildcard *.v)
AUXS := $(patsubst %.v,.%.aux,$(SRCS))

all: Makefile.coq
	+$(MAKE) -f Makefile.coq $(CORES) all

Makefile.coq: Makefile $(SRCS)
	coq_makefile -R $(STLC) Stlc $(SRCS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f $(AUXS)
	rm -f Makefile.coq

realclean: clean
	rm -f *.vo *.glob *.v.d *~ *.aux

.PHONY: all clean
