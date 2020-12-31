donotanalyze(
    'a set implies another but is not obtained by bclose on pheads',
    False,
    'ab=ed', 'b=c', 'a=f')

analyze(
    'it is instead obtained if just a single variable is in both rcn and p',
    False,
    'ab=ed', 'b=c')

donotanalyze(
    'a set implies another but is not obtained by bclose on pheads',
    False,
    'a->x', 'abx=ed', 'b=c', 'a=f')

donotanalyze(
    'a set implies another but is not obtained by bclose on pheads',
    False,
    'abg=edg', 'b=c', 'a=f')

donotanalyze(
    'a set implies another but is not obtained by bclose on pheads',
    False,
    'abg=edg', 'b=c', 'a=f', 'abg=hij')

