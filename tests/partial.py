analyze(
    'a formula that requires a partial implication',
    True,
    'ab->c', 'ac->d', 'ad->b', 'ad->e', 'bcde->a')

analyze(
    'a formula that requires two partial implications',
    Check,
    'abf->c', 'acf->d', 'adf->b',
    'adf->e',
    'bcdef->g', 'bfg->h',
    'bfh->i', 'bih->j', 'bjh->f',
    'bjh->l',
    'bfijl->a')

analyze(
    'a formula that requires two partial implications only',
    True,
    'abc->d', 'acd->e', 'ade->b', 'aeb->c', 'aeb->f', 'bcef->a')

