analyze(
    'incomparable minimal bodies (minus-one-incomparable.fig)',
    True,
    'ab->d', 'ad->b', 'bd->a',
    'ef->h', 'eh->f', 'fh->e',
    'dh->x')

analyze(
    'extra clauses added',
    True,
    'ab->d', 'ad->b', 'bd->a',
    'ef->h', 'eh->f', 'fh->e',
    'dh->x',
    'abh->x',
    'efd->x')

