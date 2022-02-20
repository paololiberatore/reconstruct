analyze(
    'a single-head equivalent formula',
    True,
    'a->b', 'b->a', 'b->c', 'a->d', 'a->e', 'c->d'
)

analyze(
    'a formula that is not single-head equivalent',
    False,
    'a->b', 'b->a', 'b->c', 'a->d', 'a->e', 'c->d', 'f->d'
)

