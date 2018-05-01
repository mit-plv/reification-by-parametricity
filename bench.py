#!/usr/bin/env python2
from __future__ import with_statement, print_function
import re, sys, math, json, gzip

STATS_RES = [re.compile(r'Doing (%s)\s+\(n= ([0-9]+) \) on ([^ ]+) with ([^ ]+) :\nTactic call ran for ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\)' % ty,
                        flags=re.DOTALL|re.MULTILINE)
             for ty in ('identity cbv', 'identity lazy', 'identity vm_compute', 'identity native_compute', 'identity simpl', 'identity cbn', 'refine let', 'cbv Denote', 'lazy Denote', 'cbn Denote', 'simpl Denote', 'transitivity')]

NON_REIF_RES = [re.compile(res, flags=re.DOTALL|re.MULTILINE) for res in
                [r'(Aggregate) time \(n= ([0-9]+) \) for "([^"]+)" with ([^ ]+) :\nTactic call aggregate ran for ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\)'] +
                [(r'Doing (%s)\s+\(n= ([0-9]+) \) for "([^"]+)" with ([^ ]+) :\nTactic call %s ran for ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\)' % (ty, ty))
                 for ty in ('cbv', 'pre', 'post', 'parsing', 'parsing elaborated', 'printing')]]

REIF_PRE_RE = re.compile(r'Doing reif\s+\(n= ([0-9]+) \) for "([^"]+)" with ([^ ]+) :\n' +
                         r'(Tactic call .*?\n' +
                         r'Tactic call reif ran for [^\n]+)',
                         flags=re.DOTALL|re.MULTILINE)
REIF_RE = re.compile('Tactic call ([^\n]*?) ran for ([0-9\.]+) secs \(([0-9\.]+)u,([0-9\.]+)s\)',
                     flags=re.DOTALL|re.MULTILINE)

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def fix_num(val):
    if val == '0.': return '0'
    return val

def fix_times(real, user, system):
    return (fix_num(real), fix_num(user), fix_num(system))

def dict_set(d, value, *keys):
    keys = tuple(map(str, keys))
    for k in keys[:-1]:
        d[k] = d.get(k, {})
        d = d[k]
    d[keys[-1]] = value

def dict_append(d, value, *keys):
    keys = tuple(map(str, keys))
    for k in keys[:-1]:
        d[k] = d.get(k, {})
        d = d[k]
    d[keys[-1]] = d.get(keys[-1], [])
    d[keys[-1]].append(value)

def average(values):
    values = list(values)
    if len(values) == 1: return values[0]
    return (('%%.0%df' % (3 + int(math.ceil(math.log(len(values))))))
            % (sum(map(float, values)) / len(values)))

def update_dict_with(d1, d2):
    for k, v in d2.items():
        if k not in d1.keys():
            d1[k] = v
        elif isinstance(v, dict):
            assert(isinstance(d1[k], dict))
            d1[k] = update_dict_with(d1[k], v)
        elif isinstance(v, list) or isinstance(v, tuple):
            d1[k] = list(d1[k]) + list(v)
    return d1

def process(fnames, ret={}):
    if len(fnames) > 1:
        for fname in fnames:
            ret = process([fname], ret)
        return ret
    contents = ''
    for fname in fnames:
        if fname[-len('.json.gz'):] == '.json.gz':
            with gzip.open(fname, 'rt') as f:
                val = json.load(f)
            ret = update_dict_with(ret, val)
        elif fname[-len('.json'):] == '.json':
            with open(fname, 'r') as f:
                val = json.load(f)
            ret = update_dict_with(ret, val)
        else:
            with open(fname, 'r') as f:
                contents += f.read() + '\n'


    contents = contents.replace('Tactic call\n', 'Tactic call ')
    contents = contents.replace('parsing elaborated', 'parsing')
    # contents = contents.replace(':\nTactic call ran', ': Tactic call ran')

    parsing_printing_kind_reps = {'Parsing':'parsing', 'ParsingElaborated':'parsing elaborated', 'Printing':'printing'}

    for reg in STATS_RES:
        for name, count, kind, const, real, user, system in reg.findall(contents):
            assert(kind == 'PHOAS')
            dict_append(ret, fix_times(real, user, system), const, name, 'Stats', count)

    for reg in NON_REIF_RES:
        for name, count, kind, const, real, user, system in reg.findall(contents):
            if kind in parsing_printing_kind_reps.keys():
                dict_append(ret, fix_times(real, user, system), const, parsing_printing_kind_reps[kind], 'Stats', count)
                if kind != 'Printing':
                    dict_append(ret, fix_times(real, user, system), const, kind, 'actual reif', count)
                    dict_append(ret, fix_times(real, user, system), const, kind, 'reif', count)
                    dict_append(ret, fix_times(real, user, system), const, kind, 'norm reif', count)
            else:
                dict_append(ret, fix_times(real, user, system), const, kind, name, count)

    for count, kind, const, body in REIF_PRE_RE.findall(contents):
        for name, real, user, system in REIF_RE.findall(body):
            dict_append(ret, fix_times(real, user, system), const, kind, name, count)

    #for const, d2 in sorted(ret.items()):
    #    for kind, d3 in sorted(d2.items()):
    #        if kind == 'Mtac2':
    #            del d2[kind]

    return ret

def collapse_times(times):
    return (average(real for real, user, system in times),
            average(user for real, user, system in times),
            average(system for real, user, system in times))

def cmp_for_kind(d, const, name):
    def do_cmp(kind1, kind2):
        if kind1 == kind2: return cmp(kind1, kind2)
        if kind1 in d[const].keys() and kind2 in d[const].keys():
            if name in d[const][kind1].keys() and name in d[const][kind2].keys():
                count1, times1 = sorted(d[const][kind1][name].items())[-1]
                count2, times2 = sorted(d[const][kind2][name].items())[-1]
                real1, user1, system1 = collapse_times(times1)
                real2, user2, system2 = collapse_times(times2)
                return cmp((count1, -float(real1), -float(user1), -float(system1), kind1),
                           (count2, -float(real2), -float(user2), -float(system2), kind2))
            elif name in d[const][kind1].keys(): return -1
            elif name in d[const][kind2].keys(): return 1
            else: return cmp(kind1, kind2)
        elif kind1 in d[const].keys(): return -1
        elif kind2 in d[const].keys(): return 1
        else: return cmp(kind1, kind2)
    return do_cmp

def print_mathematica(d):
    ret = ''
    ret += '(* ::Package:: *)\n\n'
    ret += 'ClearAll[data,Consts,Kinds,DataNames];\n\n'
    ret += 'Consts = {%s};\n' % ', '.join(sorted(set('"%s"' % const for const in d.keys())))
    ret += 'Kinds = {%s};\n' % ', '.join(sorted(set('"%s"' % kind for const, d2 in d.items() for kind in d2.keys())))
    ret += 'DataNames = {%s};\n' % ', '.join(sorted(set('"%s"' % name for const, d2 in d.items() for kind, d3 in d2.items() for name in d3.keys())))
    ret += '\n'
    for const, d2 in sorted(d.items()):
        for name in sorted(set(name for kind, d3 in d2.items() for name in d3.keys())):
            ret += 'KindsSortedFor["%s"]["%s"] = {%s};\n' % (const, name, ', '.join('"%s"' % kind for kind in sorted(d2.keys(), cmp=cmp_for_kind(d, const, name))))
        ret += '\n'
        for kind, d3 in sorted(d2.items()):
            for name, d4 in sorted(d3.items()):
                count_times = sorted([(int(count), collapse_times(times))
                                      for count, times in d4.items()])
                reals = [(count, real) for count, (real, user, system) in count_times]
                users = [(count, user) for count, (real, user, system) in count_times]
                systems = [(count, system) for count, (real, user, system) in count_times]
                str_reals = '{' + ', '.join('{' + ','.join(map(str, v)) + '}' for v in reals) + '}'
                str_users = '{' + ', '.join('{' + ','.join(map(str, v)) + '}' for v in users) + '}'
                str_systems = '{' + ', '.join('{' + ','.join(map(str, v)) + '}' for v in systems) + '}'
                ret += 'data["%(const)s"]["%(kind)s"]["%(name)s"]["real"] = %(str_reals)s;\n' % locals()
                ret += 'data["%(const)s"]["%(kind)s"]["%(name)s"]["user"] = %(str_users)s;\n' % locals()
                ret += 'data["%(const)s"]["%(kind)s"]["%(name)s"]["system"] = %(str_systems)s;\n' % locals()
    return ret

def print_json(d):
    return json.dumps(d)

def print_json_gz(d, fname):
    ret = json.dumps(d)
    with gzip.open(fname, 'wb') as f:
        f.write(ret)

if __name__ == '__main__':
    args = sys.argv[1:]
    do_mathematica = '--mathematica' in args
    do_json = '--json' in args
    do_json_gz = [arg[len('--json.gz='):] for arg in args if arg.startswith('--json.gz=')]
    args = [arg for arg in args if arg not in ('--mathematica', '--json') and not arg.startswith('--json.gz=')]
    fnames = ['bench.log']
    if len(args) > 0: fnames = args
    d = process(fnames)
    if do_mathematica:
        print(print_mathematica(d))
    if do_json:
        print(print_json(d))
    for fname in do_json_gz:
        print_json_gz(d, fname)
