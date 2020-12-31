analyze(
    'clauses entailed but not containing',
    True,
    'a=b', 'b=c',	# realized by either a->b->c->a or c->b->a->c
    'ad->b', 'ae->c'	# none of them has clauses contained in both these
)

