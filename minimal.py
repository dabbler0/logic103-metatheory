class Expression:
    def __init__(self, op, atom, sub):
        self.op = op
        self.atom = atom
        self.sub = sub

    def __repr__(self):
        sub_repr = [x.__repr__() for x in self.sub]

        if self.op == 'atom':
            return self.atom
        elif self.op == 'not':
            return '(-%s)' % sub_repr[0]
        elif self.op == 'and':
            return '(%s & %s)' % (sub_repr[0], sub_repr[1])
        elif self.op == 'or':
            return '(%s v %s)' % (sub_repr[0], sub_repr[1])
        elif self.op == 'cond':
            return '(%s -> %s)' % (sub_repr[0], sub_repr[1])
        elif self.op == 'bicond':
            return '(%s <-> %s)' % (sub_repr[0], sub_repr[1])

    def evaluate(self, mapping):
        sub_eval = [x.evaluate(mapping) for x in self.sub]
        
        if self.op == 'atom':
            return mapping[self.atom]
        elif self.op == 'not':
            return not sub_eval[0]
        elif self.op == 'and':
            return sub_eval[0] and sub_eval[1]
        elif self.op == 'or':
            return sub_eval[0] or sub_eval[1]
        elif self.op == 'cond':
            return (not sub_eval[0]) or sub_eval[1]
        elif self.op == 'bicond':
            return sub_eval[0] == sub_eval[1]

def generate_expressions(vocabulary, length):
    if length == 0:
        for v in vocabulary:
            yield Expression('atom', v, [])
    else:
        less_one = generate_expressions_memo(vocabulary, length - 1)
        for candidate in less_one:
            yield Expression('not', None, [candidate])

        for l in range(0, length - 1):
            left = generate_expressions_memo(vocabulary, l)
            right = generate_expressions_memo(vocabulary, length - 1 - l)

            for left_candidate in left:
                for right_candidate in right:
                    for op in ['and', 'or', 'cond', 'bicond']:
                        yield Expression(op, None, [left_candidate, right_candidate])

memoization = {}
def generate_expressions_memo(vocabulary, length):
    if (vocabulary, length) in memoization:
        return memoization[vocabulary, length]
    result = list(generate_expressions(vocabulary, length))
    memoization[vocabulary, length] = result
    return result

table = {
    (True, True, True): True,
    (True, True, False): True,
    (True, False, True): False,
    (True, False, False): True,
    (False, True, True): False,
    (False, True, False): True,
    (False, False, True): False,
    (False, False, False): True,
}

def make_map(t):
    return {'A': t[0], 'B': t[1], 'C': t[2]}

def main():
    for i in range(10):
        expressions = generate_expressions_memo(('A', 'B', 'C'), i)

        for expression in expressions:
            if all(table[key] == expression.evaluate(make_map(key)) for key in table):
                print('FOUND')
                print(expression)
                return
        print('Found none of length', i)
main()
