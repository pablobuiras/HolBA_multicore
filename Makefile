include scripts/setup/autoenv.mk

# set make's shell to bash
SHELL := /bin/bash

##########################################################

SRCDIR        = src
EXSDIR        = examples

EXAMPLES_BASE = $(SRCDIR)/shared/examples             \
                $(SRCDIR)/tools/cfg/examples          \
                $(SRCDIR)/tools/exec/examples         \
                $(SRCDIR)/tools/lifter/examples       \
                $(SRCDIR)/tools/wp/examples

EXAMPLES_ALL  = $(EXAMPLES_BASE)                      \
                $(EXSDIR)

BENCHMARKS    = $(SRCDIR)/tools/lifter/benchmark      \
                $(SRCDIR)/tools/wp/benchmark

##########################################################

# recursive wildcard function
rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))

HOLMAKEFILE_GENS = $(call rwildcard,$(SRCDIR)/,Holmakefile.gen) \
                   $(call rwildcard,$(EXSDIR)/,Holmakefile.gen)
HOLMAKEFILES     = $(HOLMAKEFILE_GENS:.gen=)


ifdef HOLBA_HOLMAKE_AVAILABLE
HOLMAKEFILE_DIRS = $(patsubst %/,%,$(sort $(foreach file,$(HOLMAKEFILE_GENS),$(dir $(file)))))

SML_RUNS         = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_run)
SML_RUNQS        = $(foreach sml,$(call rwildcard,$(SRCDIR)/,*.sml),$(sml)_runq)

TEST_SMLS        = $(call rwildcard,$(SRCDIR)/,selftest.sml) $(call rwildcard,$(SRCDIR)/,test-*.sml) \
                   $(call rwildcard,$(EXSDIR)/,selftest.sml) $(call rwildcard,$(EXSDIR)/,test-*.sml)
TEST_EXES        = $(TEST_SMLS:.sml=.exe)
TEST_SML_RUNQS   = $(TEST_SMLS:.sml=.sml_runq)
TEST_DIRS        = $(patsubst %/,%,$(sort $(foreach sml,$(TEST_SMLS),$(dir $(sml)))))
endif

##########################################################

.DEFAULT_GOAL := all
all: show-rules
	@echo 'Please use sub-rules to build HolBA.'

show-rules:
	@echo 'Available rules:'
	@echo '     - Holmakefiles: generates `Holmakefile`s from `Holmakefile.gen` files.'
ifdef HOLBA_HOLMAKE_AVAILABLE
	@echo '     - theory: builds only src/theory/'
	@echo '     - main: builds HolBA, but without the examples or documentation'
	@echo '     - tests: builds HolBA and runs all the tests'
	@echo '     - examples-base: builds HolBA and the examples for each tool'
	@echo '     - examples-all: builds HolBA and all the examples (base + HolBA/examples/)'
	@echo '     - benchmarks: builds HolBA and all the benchmarks'
endif
	@echo '     - gendoc: generate the documentation'
	@echo '     - cleanslate: removes all files that are .gitignore-d under src/ and examples/'

##########################################################

%Holmakefile: %Holmakefile.gen $(SRCDIR)/Holmakefile.inc
	@./scripts/gen_Holmakefiles.py $<

Holmakefiles: $(HOLMAKEFILES)


$(HOLMAKEFILE_DIRS): Holmakefiles
	cd $@ && $(HOLBA_HOLMAKE) $(HOLBA_HOLMAKE_OPTS)


%.exe: %.sml Holmakefiles
	@/usr/bin/env HOLBA_HOLMAKE="$(HOLBA_HOLMAKE)" ./scripts/mk-exe.sh $(@:.exe=.sml)

# this is a target for all sml files to run as scripts,
# it properly prepares first
# it also tries to find the undefined environment variables
$(SML_RUNS):
	@make $(patsubst %/,%,$(dir $@))
	@make $(@:.sml_run=.exe)
	@source ./scripts/setup/autoenv.sh && ./scripts/run-test.sh $(@:.sml_run=.exe)

# this target is for quick running, mainly for the run-tests.sh,
# (no preparation, it is for tests where preparation is
#  done before and autoenv.sh has been sources)
%.sml_runq:
	@./scripts/run-test.sh $(@:.sml_runq=.exe)

##########################################################

ifdef HOLBA_HOLMAKE_AVAILABLE
theory:        $(SRCDIR)/theory
main:          $(SRCDIR)

examples-base: main $(EXAMPLES_BASE)
examples-all:  main $(EXAMPLES_ALL)
benchmarks:    main $(BENCHMARKS)


tests: $(TEST_EXES) $(TEST_DIRS)
	@source ./scripts/setup/autoenv.sh && ./scripts/run-tests.sh

# this target can be made with multiple jobs, the others cannot!
_run_tests: $(TEST_SML_RUNQS)
endif


gendoc:
	cd doc/gen; ./dependencies.py

cleanslate:
	git clean -fdX src
	git clean -fdX examples

##########################################################

.PHONY: Holmakefiles

ifdef HOLBA_HOLMAKE_AVAILABLE
.PHONY: $(HOLMAKEFILE_DIRS)
.PHONY: $(SML_RUNS)
endif

# note: SML_RUNQS cannot be defined phony,
# because it uses suffix rules apparently
#.PHONY: $(SML_RUNQS) 

ifdef HOLBA_HOLMAKE_AVAILABLE
.PHONY: theory main
.PHONY: tests _run_tests
.PHONY: examples-base examples-all
.PHONY: benchmarks
endif

.PHONY: gendoc cleanslate
