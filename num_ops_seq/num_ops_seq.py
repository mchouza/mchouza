from __future__ import division
from fractions import Fraction

OPS = {
    '+': lambda a, b: Fraction(a) + Fraction(b),
    '-': lambda a, b: Fraction(a) - Fraction(b),
    '*': lambda a, b: Fraction(a) * Fraction(b),
    '/': lambda a, b: Fraction(a) / Fraction(b)
}

def evaluate(tree):
    from collections import Sequence
    if isinstance(tree, Sequence):
        return OPS[tree[0]](evaluate(tree[1]), evaluate(tree[2]))
    else:
        return tree

def get_all_trees(seq):
    
    trees = [seq]
    
    # there are len(seq) - 1 stages of grouping
    for i in range(len(seq) - 1):
        new_trees = []
        for t in trees:
            # there are len(t) - 1 ways of taking adjacent element pairs
            for j in range(len(t) - 1):
                for op in OPS:
                    new_trees.append(t[:j] + [[op, t[j], t[j+1]]] + t[j+2:])
        trees = new_trees

    #assert all(len(t) == 1 for t in trees)
    trees = [t[0] for t in trees]
    #assert all(len(t) == 3 for t in trees)

    return trees

def get_all_classified_trees(seq):
    trees = get_all_trees(seq)
    classif_trees = {}
    for t in trees:
        try:
            t_val = evaluate(t)
        except ZeroDivisionError:
            continue
        if t_val not in classif_trees:
            classif_trees[t_val] = []
        classif_trees[t_val].append(t)
    return classif_trees

def frac_to_str(f):
    if f.denominator == 1:
        return str(f.numerator)
    else:
        return '%d/%d' % (f.numerator, f.denominator)

def tree_to_inf_str(t, paren=False):
    
    from collections import Sequence
    
    if not isinstance(t, Sequence):
        return str(t)
    
    if t[0] == '+':
        first = tree_to_inf_str(t[1])
        second = tree_to_inf_str(t[2])
    elif t[0] == '-':
        first = tree_to_inf_str(t[1])
        if isinstance(t[2], Sequence) and t[2][0] in ('*', '/'):
            second = tree_to_inf_str(t[2], False)
        else:
            second = tree_to_inf_str(t[2], True)
    elif t[0] == '*':
        if not isinstance(t[1], Sequence) or t[1][0] == '*':
            first = tree_to_inf_str(t[1], False)
        else:
            first = tree_to_inf_str(t[1], True)
        if not isinstance(t[2], Sequence) or t[2][0] == '*':
            second = tree_to_inf_str(t[2], False)
        else:
            second = tree_to_inf_str(t[2], True)
    else:
        first = tree_to_inf_str(t[1], True)
        second = tree_to_inf_str(t[2], True)
        
    if paren:
        return '(%s%s%s)' % (first, t[0], second)
    else:
        return '%s%s%s' % (first, t[0], second)

if __name__ == '__main__':
    classif_trees = get_all_classified_trees([4, 4, 4, 4])
    sorted_keys = sorted(classif_trees.iterkeys())
    for k in sorted_keys:
        ts = set(tree_to_inf_str(t) for t in classif_trees[k])
        print '%s:' % frac_to_str(k)
        for t in ts:
            #assert eval(t) == float(k)
            print '%s' % t
        print
