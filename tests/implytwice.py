analyze(
    'same variable required to be implied twice (two-stage-real.fig)',
    False,
    'b->d', 'e->f',
    'ab->c', 'ab->d', 'cd->a', 'cd->e',
    'ae->c', 'ae->f', 'cf->a', 'cf->b')

