PACODIR= ./paco/src/
COQINCLUDES= -R $(PACODIR) Paco -R ./euttG/ EuttG
COQC="$(COQBIN)coqc" -q $(COQINCLUDES)

COQFILES= stream euttG examples

VFILES  := $(COQFILES:%=euttG/%.v)
VOFILES := $(COQFILES:%=euttG/%.vo)
GLOBFILES := $(COQFILES:%=euttG/%.glob)

all:
	$(MAKE) -C $(PACODIR)
	$(MAKE) coq

coq: $(VOFILES)

paco:
	$(MAKE) -C

%.vo: %.v
	@echo "COQC $*.v"
	@$(COQC) $*.v

clean:
	rm -f .depend
	rm -f $(VOFILES)
	rm -f $(GLOBFILES)
	rm -rf doc/html doc/*.glob
	make -C $(PACODIR) clean
