#!/usr/bin/env bash

function construct() {
    echo 'Require Export Reify.Benchmarks.Parsing.'
    echo ''
    for i in "$@"; do
	echo 'Goal True.'
	echo "idtac \"Doing parsing (n= $i ) for \"\"Parsing\"\" with big :\";"
	echo 'restart_timer "parsing".'
	echo 'let x := constr:(fun var : Type =>'
	echo "elet a'0 := NatS (@NatO var) * NatS (@NatO var) in"
	for v in $(seq 0 $(expr $i - 1)); do
	    echo "elet a'$(expr $v + 1) := Var a'$v * Var a'$v in"
	done
	echo "Var a'$i"
	echo ') in'
	echo 'finish_timing ( "Tactic call" ) "parsing".'
	echo 'Abort.'
    done
}

if [ ! -z "$1" ]; then
    construct "$@"
else
    construct $(seq 1 500) 600 700 800 900 1000 > Parsing_quick.v
    construct $(seq 1500 500 5000) > Parsing_medium.v
    construct $(seq 6000 1000 10000) 20000 > Parsing_slow.v
fi
