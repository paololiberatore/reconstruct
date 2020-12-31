donotanalyze(
    'paths join: from x to ab and to cd, then from bd back',
    True,
    'x=ab', 'x=cd', 'bd->w', 'w->x')

donotanalyze(
    'paths join, with other variabiles in them',
    True,
    'x->y', 'x->z', 'y->ab', 'z->cd', 'ab->x', 'cd->x', 'bd->w', 'w->x')

analyze(
    'separate paths join',
    True,
    'xya->xyb', 'xyb->xyz',   # path 1 goes to xyz
    'yzd->yze', 'yze->xyz',   # path 2 goes to xyz
    'xyz->xgz',               # xyz goes to common path
    'xgz->xya', 'xgz->yzd')   # common path goes to path 1 and path 2

