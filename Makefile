PRINTING_KINDS := \
	Printing

PARSING_KINDS := \
	Parsing

PARSING_ELABORATED_KINDS := \
	ParsingElaborated

PARSING_FLAT_KINDS := \
	ParsingFlat

KINDS := $(PARSING_KINDS) $(PARSING_FLAT_KINDS) $(PARSING_ELABORATED_KINDS) \
	Stats \
	TypeClasses \
	LtacPrimUncurry \
	LtacVariants \
	CanonicalStructures \
	Mtac2 \
	Ltac2 \
	OCaml \
	TemplateCoq \
	QuoteFlat \
	Parametricity

.PHONY: coq
coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: clean
clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	@ rm -f Makefile.coq

QUICK_NORMAL_LOGS := $(KINDS:%=Benchmarks/%_quick.log)
MEDIUM_NORMAL_LOGS := $(KINDS:%=Benchmarks/%_medium.log)
SLOW_NORMAL_LOGS := $(KINDS:%=Benchmarks/%_slow.log)

QUICK_PARSING_LOGS := $(PARSING_KINDS:%=Benchmarks/%_quick.log)
MEDIUM_PARSING_LOGS := $(PARSING_KINDS:%=Benchmarks/%_medium.log)
SLOW_PARSING_LOGS := $(PARSING_KINDS:%=Benchmarks/%_slow.log)

QUICK_PARSING_FLAT_LOGS := $(PARSING_FLAT_KINDS:%=Benchmarks/%_quick.log)
MEDIUM_PARSING_FLAT_LOGS := $(PARSING_FLAT_KINDS:%=Benchmarks/%_medium.log)
SLOW_PARSING_FLAT_LOGS := $(PARSING_FLAT_KINDS:%=Benchmarks/%_slow.log)

QUICK_PARSING_ELABORATED_LOGS := $(PARSING_ELABORATED_KINDS:%=Benchmarks/%_quick.log)
MEDIUM_PARSING_ELABORATED_LOGS := $(PARSING_ELABORATED_KINDS:%=Benchmarks/%_medium.log)
SLOW_PARSING_ELABORATED_LOGS := $(PARSING_ELABORATED_KINDS:%=Benchmarks/%_slow.log)

QUICK_PRINTING_LOGS := $(PRINTING_KINDS:%=Benchmarks/%_quick.log)
MEDIUM_PRINTING_LOGS := $(PRINTING_KINDS:%=Benchmarks/%_medium.log)
SLOW_PRINTING_LOGS := $(PRINTING_KINDS:%=Benchmarks/%_slow.log)

QUICK_LOGS := $(QUICK_NORMAL_LOGS) $(QUICK_PRINTING_LOGS)
MEDIUM_LOGS := $(MEDIUM_NORMAL_LOGS) $(MEDIUM_PRINTING_LOGS)
SLOW_LOGS := $(SLOW_NORMAL_LOGS) $(SLOW_PRINTING_LOGS)

NORMAL_LOGS := $(QUICK_NORMAL_LOGS) $(MEDIUM_NORMAL_LOGS) $(SLOW_NORMAL_LOGS)
PARSING_LOGS := $(QUICK_PARSING_LOGS) $(MEDIUM_PARSING_LOGS) $(SLOW_PARSING_LOGS)
PARSING_FLAT_LOGS := $(QUICK_PARSING_FLAT_LOGS) $(MEDIUM_PARSING_FLAT_LOGS) $(SLOW_PARSING_FLAT_LOGS)
PARSING_ELABORATED_LOGS := $(QUICK_PARSING_ELABORATED_LOGS) $(MEDIUM_PARSING_ELABORATED_LOGS) $(SLOW_PARSING_ELABORATED_LOGS)
PRINTING_LOGS := $(QUICK_PRINTING_LOGS) $(MEDIUM_PRINTING_LOGS) $(SLOW_PRINTING_LOGS)
LOGS := $(QUICK_LOGS) $(MEDIUM_LOGS) $(SLOW_LOGS)

.PHONY: bench quick-bench medium-bench slow-bench
bench:
	$(MAKE) $(LOGS)
	$(MAKE) bench.log

quick-bench:
	$(MAKE) $(QUICK_LOGS)
	$(MAKE) bench.log

medium-bench:
	$(MAKE) $(MEDIUM_LOGS)
	$(MAKE) bench.log

slow-bench:
	$(MAKE) $(SLOW_LOGS)
	$(MAKE) bench.log

.PHONY: parsing-args
parsing-args:
	echo "$$(seq 1 500)" > Benchmarks/Parsing_quick.args
	echo "$$(seq 505 5 1000) $$(seq 1010 10 2000) $$(seq 2050 50 5000)" > Benchmarks/Parsing_medium.args
	echo "$$(seq 5050 50 10000) $$(seq 10100 100 20000)" > Benchmarks/Parsing_slow.args
	echo "$$(seq 1 500) $$(seq 500 5 1000)" > Benchmarks/ParsingElaborated_quick.args
	echo "$$(seq 1010 10 2000) $$(seq 2050 50 5150)" > Benchmarks/ParsingElaborated_medium.args
	echo "$$(seq 5200 50 10000) $$(seq 10100 100 20000)" > Benchmarks/ParsingElaborated_slow.args
	echo "$$(seq 1 500) $$(seq 500 5 1000)" > Benchmarks/ParsingFlat_quick.args
	echo "$$(seq 1010 10 2000) $$(seq 2050 50 5000)" > Benchmarks/ParsingFlat_medium.args
	echo "$$(seq 5050 50 10000) $$(seq 10100 100 20000)" > Benchmarks/ParsingFlat_slow.args

$(QUICK_LOGS) : Benchmarks/%_quick.log : Benchmarks/%.vo
$(MEDIUM_LOGS) : Benchmarks/%_medium.log : Benchmarks/%.vo
$(SLOW_LOGS) : Benchmarks/%_slow.log : Benchmarks/%.vo

$(PARSING_LOGS:.log=.v) : %.v : Benchmarks/make_test_parsing.sh %.args
	./Benchmarks/make_test_parsing.sh $$(cat $*.args) > $@

$(PARSING_FLAT_LOGS:.log=.v) : %.v : Benchmarks/make_test_parsing_flat.py %.args
	./Benchmarks/make_test_parsing_flat.py $$(cat $*.args) > $@

$(PARSING_ELABORATED_LOGS:.log=.v) : %.v : Benchmarks/make_test_parsing_elaborated.sh %.args
	./Benchmarks/make_test_parsing_elaborated.sh $$(cat $*.args) > $@

.PHONY: parsing-test-files
parsing-test-files: $(PARSING_LOGS:.log=.v) $(PARSING_FLAT_LOGS:.log=.v) $(PARSING_ELABORATED_LOGS:.log=.v)

$(NORMAL_LOGS) : Benchmarks/%.log : Benchmarks/%.v
	$(COQBIN)coqc -q -Q . Reify -I . $< > $@.tmp && mv -f $@.tmp $@

$(PRINTING_LOGS) : Benchmarks/%.log : Benchmarks/%.v
	rm -f $@.ok
	($(COQBIN)coqc -q -Q . Reify -I . $<; touch $@.ok) | grep -v 'elet' | grep -v 'expr' | grep -v 'fun var' > $@.tmp && mv -f $@.tmp $@
	rm $@.ok

.PHONY: bench.log bench.tmp.log
bench.log bench.tmp.log:
	@echo 'Aggregating logs ($(wildcard $(LOGS)))'
	echo | cat $(wildcard $(LOGS)) > bench.log
	echo | cat $(wildcard $(LOGS) $(LOGS:%=%.tmp)) > bench.tmp.log

.PHONY: compress-extra-logs
compress-extra-logs: EXTRA_LOGS=$(wildcard extra-logs/*.log extra-logs/*.json extra-logs/*.json.gz)

compress-extra-logs:
	mkdir -p extra-logs/bak
	./bench.py --json.gz=extra-logs/aggregate.json.gz.tmp $(EXTRA_LOGS)
	mv -f -t extra-logs/bak $(EXTRA_LOGS)
	mv extra-logs/aggregate.json.gz.tmp extra-logs/aggregate.json.gz

bench.wl: bench.log bench.py $(wildcard extra-logs/*.log extra-logs/*.json extra-logs/*.json.gz)
	./bench.py --mathematica bench.log $(wildcard extra-logs/*.log extra-logs/*.json extra-logs/*.json.gz) > bench.wl

bench.tmp.wl: bench.tmp.log bench.py $(wildcard extra-logs/*.log extra-logs/*.json extra-logs/*.json.gz)
	./bench.py --mathematica bench.tmp.log $(wildcard extra-logs/*.log extra-logs/*.json extra-logs/*.json.gz) > bench.tmp.wl
