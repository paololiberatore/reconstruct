#!/usr/bin/env python3
#
# single-head equivalence:
# is the given formula equivalent to a single-head formula,
# one where each variable occurs in the head of at most one clause?

import itertools
import sys


# print up to a certain level of nesting

maxlevel = 2
def printinfo(level, *s):
    if level <= maxlevel:
        if level > 1:
            print(' ' * (8 * (level - 1) - 1), end = '')
        for e in s:
            if e == '\\nonl':
                break;
            print(e, end = ' ')
        else:
            print()


# make a formula from a collection of lists

def clause(s):
    if isinstance(s, list):
        return frozenset([frozenset(s)])
    elif '=' in s:
        h = s.split('=')
        return clause(h[0] + '->' + h[1]) | clause(h[1] + '->' + h[0])
    else:
        all = frozenset()
        body = set()
        sign = '-'
        for c in s:
            if c == '>':
                sign = ''
            elif c == '-':
                pass
            elif sign == '-':
                body |= {sign + c}
            else:
                all |= {frozenset(body | {sign + c})}
        return all

def formula(*l):
    return set().union(*{clause(x) for x in l})


# from clause to string

def clausetostring(clause, pretty = True):
    if pretty:
        return ''.join({l[1:] for l in clause if l[0] == '-'}) + '->' + \
               ''.join({l for l in clause if l[0] != '-'})
    else:
        return '(' + ' '.join(clause) + ')'


# from formula to string

def formulatostring(formula, label = None, pretty = True):
    s = label + ' ' if label else ''
    s += ' '.join(clausetostring(c, pretty) for c in formula)
    return s


# print a formula

def formulaprint(formula, label = None, pretty = True):
    print(formulatostring(formula, label, pretty))


# size of a formula, as total occurrencies of variables

def formulasize(a):
    return sum([len(x) for x in a])


# check whether a clause is a tautology

def tautology(c):
    for l in c:
        if '-' + l in c:
            return True
    return False


# remove tautologies from a formula

def detautologize(s):
    return {c for c in s if not tautology(c)}


# resolve two clauses; emptyset if they don't resolve or resolve to a tautology

def resolve(a, b):
    for x in a:
        for y in b:
            if x == '-' + y or '-' + x == y:
                r = a.difference([x]).union(b.difference([y]))
                return set() if tautology(r) else set({r})
    return set()


# minimal (not containing others) clauses of a formula

def minimal(s, e = set()):
   r = set()
   for c in s:
       for d in s | e:
           if d < c:
               break
       else:
           r |= {c}
   return r


# resolution closure, minimized

def close(s):
    r = set()
    n = s.copy()
    while n != r:
        r = n.copy()
        for a in r:
           for b in r:
               n |= resolve(a, b)
        n = minimal(n)
    return n


# check equivalence

def equivalent(s, r):
    return minimal(close(detautologize(s))) == minimal(close(detautologize(r)))


# check whether a formula is single-head

def issinglehead(e):
    h = [h for c in e for h in c if h[0] != '-']
    return len(h) == len(set(h))


# head and body

def head(c):
    return next((l for l in c if l[0] != '-'))

def heads(f):
    return {head(c) for c in f}

def body(c):
    return {l[1:] for l in c if l[0] == '-'}

def bodies(f):
    return {frozenset(body(c)) for c in f}


# rcn and ucl

def rcnucl(b, f):
    heads = set()
    usable = set()
    prev = None
    while heads != prev:
        prev = heads.copy()
        for c in f:
            if body(c) <= b | heads:
                 usable |= {c}
                 heads |= {head(c)}
    return heads,minimal(usable)


# h-closure: minimal consequences of usable with head in heads

def hclose(heads, usable):
    closure = {c for c in usable if head(c) in heads}
    closure = minimal(closure)
    resolved = set()
    toresolve = closure - resolved
    while toresolve:
        for c in toresolve:
            for u in usable:
                closure |= {n for n in resolve(c, u) \
			if head(n) == head(c) and not tautology(n)}
        resolved |= toresolve
        closure = minimal(closure)
        toresolve = closure - resolved
    return closure


# minimal bodies

def minbodies(minbcl, uclscl):
    done = set()
    min = set()
    for b in minbcl:
        if b in done or body(b) in min:
            continue
        printinfo(2, 'start:', clausetostring(b))
        trace = set({b})               # clauses found in this run
        done |= {b}                    # all clauses found so far
        bprev = None
        while bprev != b:
            bprev = b
            for c in uclscl:
                if body(c) <= body(b):
                    # check whether uclscl, bc |= b
                    for bc in minbcl:
                        if '-' + head(c) in bc:
                            if b == (bc | c) - {head(c), '-' + head(c)}:
                                break
                    else:
                        continue;
                    printinfo(2, '    next:', clausetostring(bc), '\\nonl')
                    # do not loop
                    if bc in trace:
                        printinfo(2, 'in trace')
                        continue
                    # clause already solved or body already minimal
                    if bc in done or body(bc) in min:
                        printinfo(2, 'in done or min')
                        bprev = b
                        break
                    printinfo(2)
                    b = bc
                    trace |= {b}
                    done |= {b}
            else:
                if bprev == b:
                    min |= {frozenset(body(b))}
                    printinfo(2, formulatostring(min, '    min:', False))
    return min


# single-head equivalence

def reconstruct(f):
    printinfo(1, formulatostring(f, 'clausal:'))
    f = detautologize(f)
    f = minimal(f)
    printinfo(1, formulatostring(f, 'simplified:'))
    printinfo(1, 'single head:', issinglehead(f))

    # for each body B in F, determine RCN(B,F) and UCL(B,F)

    preconditions = bodies(f)
    rcn = {}                            # rcn[b] = RCN(B,F)
    ucl = {}                            # ucl[b] = UCL(B,F)
    for p in preconditions:
         rcn[p],ucl[p] = rcnucl(p, f)

    # cycle over preconditions

    constructed = formula()
    cbodies = set()                     # bodies of the clauses of G
    bodied = set()                      # heads of the clauses of G
    used = set()                        # clauses of F used so far
    while preconditions:
        formulaprint(constructed, 'constructed:')
        formulaprint(used, 'used:')
        printinfo(1, 'bodied:', ' '.join(bodied))

        # find a minimal precondition, based on B+RCN(B,F) = BCN(B,F)

        p = next(iter(preconditions))
        for t in preconditions:
            if rcn[t] | t < rcn[p] | p:
                p = t
        preconditions -= \
            {t for t in preconditions if t.issubset(rcn[p] | p)}

        # heads

        printinfo(1, 'preconditions:', ' '.join(p))
        printinfo(1, '    rcn[p]:', ' '.join(rcn[p]))
        pheads = list(rcn[p] - bodied)
        maxit = set(pheads) | rcnucl(p | set(pheads), constructed)[0]
        printinfo(1, '    maxit:', ' '.join(maxit))
        if not rcn[p] <= maxit:
            printinfo(1, '    insufficient heads')
            return None

        # bodies

        headbodies = hclose(pheads, ucl[p])
        formulaprint(headbodies, '    headbodies:')
        pbodies = minbodies(headbodies, ucl[p] & used)
        inbodies = set().union(*bodies(headbodies)) - cbodies
        printinfo(1, '    heads:', ' '.join(pheads))
        formulaprint(pbodies, '    bodies:', False)
        printinfo(1, '    inbody:', ' '.join(inbodies))

        # target

        headless = hclose(rcn[p] & bodied, ucl[p])
        formulaprint(headless, '    headless:')

        headlessbodies = set().union(*bodies(headless)) - cbodies - inbodies
        if headlessbodies:
            printinfo(1, '    unachievable:', ' '.join(headlessbodies))
            return None

        ptarget = headbodies | headless
        formulaprint(ptarget, '    target:')
        if ptarget == set():
            printinfo(1, '    empty target')
            continue

        # test all combinations of heads and bodies

        for c in itertools.product(pbodies, repeat = len(pheads)):
            formulaprint(c, '    body list:', False)

            # do bodies includes everything they are supposed to?

            allbodies = {l for e in c for l in e}
            if not inbodies | headlessbodies <= allbodies:
                printinfo(1, '    insufficient bodies:', ''.join(allbodies))
                continue

            # build the combination

            it = set()
            skip = False
            for h,b in zip(pheads, c):
                if h in b:
                    skip = True
                    break
                it |= {frozenset({'-' + l for l in b} | {h})}
            if skip:
                printinfo(1, '    tautology:', ''.join(b) + '->' + h)
                continue

            # check equality of variables entailed by p

            gitrcn,gitucl = rcnucl(p, constructed | it)
            if gitrcn != rcn[p]:
                printinfo(1, formulatostring(it, '    !rcn[precondition]:'))
                continue

            # check equality of all minimal bodies

            noteq = False
            for b in pbodies:
                if rcnucl(b, constructed | it)[0] != rcn[p]:
                    printinfo(1,
                        formulatostring(it, '    !rcn[' + ''.join(b) + ']:'))
                    noteq = True
                    break
            if noteq:
                continue

            # check whether G + combination implies target

            cl = hclose(gitrcn, gitucl)
            if ptarget == cl:
                printinfo(1, formulatostring(it, '    equivalent:'))
                break
            printinfo(1, formulatostring(it, '    not equivalent:'))
            printinfo(2, formulatostring(gitucl, '    gitucl:'))
            printinfo(2, formulatostring(constructed, '    constructed:'))
            printinfo(2, formulatostring(cl, '    hclose:'))
            printinfo(2, formulatostring(ptarget - cl, '    target - hclose:'))
        else:
            return None

        # entailment obtained: update G and related sets

        used |= ucl[p]
        bodied |= set(pheads)
        cbodies |= allbodies
        constructed |= it
        printinfo(1, formulatostring(constructed, '    constructed:'))

    return constructed


# analyze a formula

Check='Check'
def analyze(d, result, *s):
    print('##', d, '##')
    print('formula:', ' '.join(s))
    f = formula(*s)

    if result == Check:
        printinfo(1, formulatostring(f, 'clausal:'))
        f = detautologize(f)
        f = minimal(f)
        printinfo(1, formulatostring(f, 'simplified:'))
        printinfo(1, 'single head:', issinglehead(f))
        print()
        return

    sh = reconstruct(f)
    if sh == None:
        print('not single-head equivalent')
    else:
        formulaprint(sh, 'single-head form:')
        print('single-head:', issinglehead(sh))
        print('equivalent:', equivalent(sh, f))
    if result != None:
        if (sh != None) == result:
            print('TEST PASSED')
        else:
            print('*** TEST FAILED ******************')

    print()


# do not analyze a formula

def donotanalyze(d, result, *s):
    pass


# commandline arguments

if len(sys.argv) <= 1 or sys.argv[1] == '-h':
    if len(sys.argv) <= 1:
        print('no argument')
    print('usage:')
    print('\tsinglehead.py [-t] testfile.py')
    print('\tsinglehead.py -f clause clause...' )
    print('\t\tclause: ab->c, ab=c, abc (= a or b or c)')
elif sys.argv[1] == '-f':
    analyze('cmdline formula', None, *sys.argv[2:])
elif sys.argv[1] == '-t':
    exec(open(sys.argv[2]).read())
else:
    exec(open(sys.argv[1]).read())

