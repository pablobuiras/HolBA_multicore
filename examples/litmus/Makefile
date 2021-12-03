HOL=../../opt/hol_k14/bin/hol
POLYC=../../opt/polyml_v5.8.1/bin/polyc

.PHONY: all
all: lift_test run_test

%.o: %.sml
	$(HOL) -q $< <<< "val _ = PolyML.export(\"$*\", main)"

lift_test: lift_test.o 
	$(POLYC) $< -o $@

run_test: run_test.o 
	$(POLYC) $< -o $@
