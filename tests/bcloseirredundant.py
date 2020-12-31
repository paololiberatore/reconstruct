analyze(
    'bclose does not remove non-minimal clause, irredundant',
    False,
    'ab->c', 'cd->e', 'a->f', 'f->e'
)

