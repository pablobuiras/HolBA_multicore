HOL=../../opt/hol_k14/bin/hol
POLYC=../../opt/polyml_v5.8.1/bin/polyc

SHELL=/bin/bash

.PHONY: all clean
all: lift_test run_test
clean:
	rm -f lift_test run_test *.o

.PHONY: heap
heap:
	../../opt/hol_k14/bin/Holmake

%.o: %.sml heap
	$(HOL) -q $< <<< "val _ = PolyML.export(\"$*\", main)" >/dev/null

lift_test: lift_test.o 
	$(POLYC) $< -o $@

run_test: run_test.o 
	$(POLYC) $< -o $@
