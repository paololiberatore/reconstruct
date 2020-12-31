analyze(
    'a formula that is single-head on every single variable',
    False,
    'a->b', 'b->c', 'c->b')

analyze(
    'a formula equivalent to the above but single-head on b',
    False,
    'a->c', 'b->c', 'c->b')

