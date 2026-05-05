COQC ?= coqc
COQFLAGS ?= -Q theories ZkProver

VOFILES := theories/ZkProver/SatUnsat.vo

.PHONY: all clean

all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

clean:
	find theories \( -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' -o -name '.*.aux' \) -type f -print | xargs -r rm -f
