#!/usr/bin/env python2

import sys

def expr_of_count(i, elaborated):
    if i <= 1:
        if elaborated:
            return '(@NatS var (@NatO var))'
        else:
            return '(NatS (@NatO var))'
    elif i % 2 == 0:
        subterm = expr_of_count(i / 2, elaborated)
        if elaborated:
            return '(@NatMul var %s %s)' % (subterm, subterm)
        else:
            return '(%s * %s)' % (subterm, subterm)
    else:
        one = expr_of_count(1, elaborated)
        subterm = expr_of_count(i - 1, elaborated)
        if elaborated:
            return '(@NatMul var %s %s)' % (one, subterm)
        else:
            return '(%s * %s)' % (one, subterm)

def construct(nums):
    print('Require Export Reify.Benchmarks.ParsingFlat.')
    print('')
    for i in nums:
        print('Goal True.')
        print('idtac "Doing parsing (n= %d ) for ""ParsingElaborated"" with big_flat :";' % i)
        print('restart_timer "parsing".')
	print('let x := constr:(fun var : Type =>')
        print('(%s)%%expr' % expr_of_count(i, True))
        print(') in')
	print('finish_timing ( "Tactic call" ) "parsing".')
	print('Abort.')
	print('Goal True.')
	print('idtac "Doing parsing (n= %d ) for ""Parsing"" with big_flat :";' % i)
	print('restart_timer "parsing".')
	print('let x := constr:(fun var : Type =>')
        print('(%s)%%expr' % expr_of_count(i, False))
        print(') in')
	print('finish_timing ( "Tactic call" ) "parsing".')
	print('Abort.')

if __name__ == '__main__':
    construct(map(int, sys.argv[1:]))
