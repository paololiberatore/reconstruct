analyze(
    'the algorithm takes linear time',
    True,
    'a->b', 'b->c', 'c->d', 'd->e'
)

analyze(
    'the algorithm may take exponential time',
    False,
    'a->b', 'b->c', 'c->d', 'd->e', 'e->a',
    'a->z',
    'y->z',
    'y->x', 'x->w', 'w->v', 'v->u', 'u->y'
)
