# bclose() is syntax-dependent without minimization;
# to check, add "return s" as the first line of minimal(),
# possibly change '<' to '<=' in condition 'rcn[t] | t < rcn[p] | p';
# then compare the ptargets for precondition ac

analyze(
    'syntax-dependency when not minimizing: first formula',
    True,
    'a=b', 'ca->d', 'abc->d')

analyze(
    'syntax-dependency when not minimizing: second formula',
    True,
    'a=b', 'ac->d')

