#!/usr/bin/env bash

function construct() {
    echo 'Require Export Reify.Benchmarks.ParsingElaborated.'
    echo ''
    for i in "$@"; do
	echo 'Goal True.'
	echo "idtac \"Doing parsing (n= $i ) for \"\"ParsingElaborated\"\" with big :\";"
	echo 'restart_timer "parsing".'
	echo 'let x := constr:(fun var : Type =>'
	echo "@LetIn var (@NatMul var (@NatS var (@NatO var)) (@NatS var (@NatO var))) (fun a'0 : var =>"
	for v in $(seq 0 $(expr $i - 1)); do
	    echo "@LetIn var (@NatMul var (@Var var a'$v) (@Var var a'$v)) (fun a'$(expr $v + 1) : var =>"
	done
	echo "@Var var a'$i"
	for v in $(seq 0 $(expr $i - 1)); do
	    echo -n ')'
	done
	echo ')) in'
	echo 'finish_timing ( "Tactic call" ) "parsing".'
	echo 'Abort.'
    done
}

if [ ! -z "$1" ]; then
    construct "$@"
else
    construct $(seq 1 500) 600 700 800 900 1000 > ParsingElaborated_quick.v
    construct $(seq 1500 500 5000) > ParsingElaborated_medium.v
    construct $(seq 6000 1000 10000) 20000 > ParsingElaborated_slow.v
fi
