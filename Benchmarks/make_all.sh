#!/usr/bin/env bash

for kind in Stats TypeClasses LtacPrimUncurry LtacVariants CanonicalStructures MTac2 Ltac2 OCaml TemplateCoq QuoteFlat Parametricity Printing; do
    for speed in quick medium slow; do
	cat > ${kind}_${speed}.v <<EOF
Require Export Reify.Benchmarks.${kind}.

Goal True.
  do_test_${kind} true ${speed}.
  do_test_${kind} false ${speed}.
Abort.
EOF
    done
done
