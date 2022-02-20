analyze(
    'the algorithm takes linear time',
    True,
    'a->b', 'b->c', 'c->d', 'd->e'
)

analyze(
    'the algorithm may take exponential time',
    False,
    'a->b', 'b->c', 'c->d', 'd->e', 'e->a', 'y->z', 'a->z'
)
