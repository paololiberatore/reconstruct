analyze(
    'fake clauses, all entailed by scl',
    True,
    'a->b', 'b->c', 'c->a',
    'd->e', 'e->f', 'f->d',
    'ad->c', 'be->a', 'cf->b')
