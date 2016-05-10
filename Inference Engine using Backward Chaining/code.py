import itertools, re


from utils import *

#______________________________________________________________________________

class KB:

    def __init__(self, sentence=None):
        abstract

    def tell(self, sentence):
        "Add the sentence to the KB."
        abstract

    def ask(self, query):
        """Return a substitution that makes the query true, or,
        failing that, return False."""
        for result in self.ask_generator(query):
            return result
        return False

    def ask_generator(self, query):
        "Yield all the substitutions that make query true."
        abstract

    def retract(self, sentence):
        "Remove sentence from the KB."
        abstract


class PropKB(KB):
    "A KB for propositional logic. Inefficient, with no indexing."

    def __init__(self, sentence=None):
        self.clauses = []
        if sentence:
            self.tell(sentence)

    def tell(self, sentence):
        "Add the sentence's clauses to the KB."
        self.clauses.extend(conjuncts(to_cnf(sentence)))

    def ask_generator(self, query):
        "Yield the empty substitution if KB implies query; else nothing."
        if tt_entails(Expr('&', *self.clauses), query):
            yield {}

    def retract(self, sentence):
        "Remove the sentence's clauses from the KB."
        for c in conjuncts(to_cnf(sentence)):
            if c in self.clauses:
                self.clauses.remove(c)

#______________________________________________________________________________

class Expr:

    def __init__(self, op, *args):
        "Op is a string or number; args are Exprs (or are coerced to Exprs)."
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = num_or_str(op)
        self.args = map(expr, args) ## Coerce args to Exprs

    def __call__(self, *args):
        """Self must be a symbol with no args, such as Expr('F').  Create a new
        Expr with 'F' as op and the args as arguments."""
        assert is_symbol(self.op) and not self.args
        return Expr(self.op, *args)

    def __repr__(self):
        "Show something like 'P' or 'P(x, y)', or '~P' or '(P | Q | R)'"
        if not self.args:         # Constant or proposition with arity 0
            return str(self.op)
        elif is_symbol(self.op):  # Functional or propositional operator
            return '%s(%s)' % (self.op, ', '.join(map(repr, self.args)))
        elif len(self.args) == 1: # Prefix operator
            return self.op + repr(self.args[0])
        else:                     # Infix operator
            return '(%s)' % (' '+self.op+' ').join(map(repr, self.args))

    def __eq__(self, other):
        """x and y are equal iff their ops and args are equal."""
        return (other is self) or (isinstance(other, Expr)
            and self.op == other.op and self.args == other.args)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        "Need a hash method so Exprs can live in dicts."
        return hash(self.op) ^ hash(tuple(self.args))

    # See http://www.python.org/doc/current/lib/module-operator.html
    # Not implemented: not, abs, pos, concat, contains, *item, *slice
    def __lt__(self, other):     return Expr('<',  self, other)
    def __le__(self, other):     return Expr('<=', self, other)
    def __ge__(self, other):     return Expr('>=', self, other)
    def __gt__(self, other):     return Expr('>',  self, other)
    def __add__(self, other):    return Expr('+',  self, other)
    def __sub__(self, other):    return Expr('-',  self, other)
    def __and__(self, other):    return Expr('&',  self, other)
    def __div__(self, other):    return Expr('/',  self, other)
    def __truediv__(self, other):return Expr('/',  self, other)
    def __invert__(self):        return Expr('~',  self)
    def __lshift__(self, other): return Expr('<<', self, other)
    def __rshift__(self, other): return Expr('>>', self, other)
    def __mul__(self, other):    return Expr('*',  self, other)
    def __neg__(self):           return Expr('-',  self)
    def __or__(self, other):     return Expr('|',  self, other)
    def __pow__(self, other):    return Expr('**', self, other)
    def __xor__(self, other):    return Expr('^',  self, other)
    def __mod__(self, other):    return Expr('<=>',  self, other)



def expr(s):

    if isinstance(s, Expr): return s
    if isnumber(s): return Expr(s)
    ## Replace the alternative spellings of operators with canonical spellings
    s = s.replace('==>', '>>').replace('<==', '<<')
    s = s.replace('<=>', '%').replace('=/=', '^')
    ## Replace a symbol or number, such as 'P' with 'Expr("P")'
    s = re.sub(r'([a-zA-Z0-9_.]+)', r'Expr("\1")', s)
    ## Now eval the string.  (A security hole; do not use with an adversary.)
    return eval(s, {'Expr':Expr})

def is_symbol(s):
    "A string s is a symbol if it starts with an alphabetic char."
    return isinstance(s, str) and s[:1].isalpha()

def is_var_symbol(s):
    "A logic variable symbol is an initial-lowercase string."
    return is_symbol(s) and s[0].islower()

def is_prop_symbol(s):
    """A proposition logic symbol is an initial-uppercase string other than
    TRUE or FALSE."""
    return is_symbol(s) and s[0].isupper() and s != 'TRUE' and s != 'FALSE'

def variables(s):
    """Return a set of the variables in expression s.
    >>> ppset(variables(F(x, A, y)))
    set([x, y])
    >>> ppset(variables(F(G(x), z)))
    set([x, z])
    >>> ppset(variables(expr('F(x, x) & G(x, y) & H(y, z) & R(A, z, z)')))
    set([x, y, z])
    """
    result = set([])
    def walk(s):
        if is_variable(s):
            result.add(s)
        else:
            for arg in s.args:
                walk(arg)
    walk(s)
    return result

def is_definite_clause(s):
    """returns True for exprs s of the form A & B & ... & C ==> D,
    where all literals are positive.  In clause form, this is
    ~A | ~B | ... | ~C | D, where exactly one clause is positive.
    >>> is_definite_clause(expr('Farmer(Mac)'))
    True
    >>> is_definite_clause(expr('~Farmer(Mac)'))
    False
    >>> is_definite_clause(expr('(Farmer(f) & Rabbit(r)) ==> Hates(f, r)'))
    True
    >>> is_definite_clause(expr('(Farmer(f) & ~Rabbit(r)) ==> Hates(f, r)'))
    False
    >>> is_definite_clause(expr('(Farmer(f) | Rabbit(r)) ==> Hates(f, r)'))
    False
    """
    if is_symbol(s.op):
        return True
    elif s.op == '>>':
        antecedent, consequent = s.args
        return (is_symbol(consequent.op)
                and every(lambda arg: is_symbol(arg.op), conjuncts(antecedent)))
    else:
        return False

def parse_definite_clause(s):
    "Return the antecedents and the consequent of a definite clause."
    assert is_definite_clause(s)
    if is_symbol(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

## Useful constant Exprs used in examples and code:
TRUE, FALSE, ZERO, ONE, TWO = map(Expr, ['TRUE', 'FALSE', 0, 1, 2])
A, B, C, D, E, F, G, P, Q, x, y, z  = map(Expr, 'ABCDEFGPQxyz')

#______________________________________________________________________________

def tt_entails(kb, alpha):
    """Does kb entail the sentence alpha? Use truth tables. For propositional
    kb's and sentences. [Fig. 7.10]
    >>> tt_entails(expr('P & Q'), expr('Q'))
    True
    """
    assert not variables(alpha)
    return tt_check_all(kb, alpha, prop_symbols(kb & alpha), {})

def tt_check_all(kb, alpha, symbols, model):
    "Auxiliary routine to implement tt_entails."
    if not symbols:
        if pl_true(kb, model):
            result = pl_true(alpha, model)
            assert result in (True, False)
            return result
        else:
            return True
    else:
        P, rest = symbols[0], symbols[1:]
        return (tt_check_all(kb, alpha, rest, extend(model, P, True)) and
                tt_check_all(kb, alpha, rest, extend(model, P, False)))

def prop_symbols(x):
    "Return a list of all propositional symbols in x."
    if not isinstance(x, Expr):
        return []
    elif is_prop_symbol(x.op):
        return [x]
    else:
        return list(set(symbol for arg in x.args
                        for symbol in prop_symbols(arg)))

def tt_true(alpha):
    """Is the propositional sentence alpha a tautology? (alpha will be
    coerced to an expr.)
    >>> tt_true(expr("(P >> Q) <=> (~P | Q)"))
    True
    """
    return tt_entails(TRUE, expr(alpha))

def pl_true(exp, model={}):
    """Return True if the propositional logic expression is true in the model,
    and False if it is false. If the model does not specify the value for
    every proposition, this may return None to indicate 'not obvious';
    this may happen even when the expression is tautological."""
    op, args = exp.op, exp.args
    if exp == TRUE:
        return True
    elif exp == FALSE:
        return False
    elif is_prop_symbol(op):
        return model.get(exp)
    elif op == '~':
        p = pl_true(args[0], model)
        if p is None: return None
        else: return not p
    elif op == '|':
        result = False
        for arg in args:
            p = pl_true(arg, model)
            if p is True: return True
            if p is None: result = None
        return result
    elif op == '&':
        result = True
        for arg in args:
            p = pl_true(arg, model)
            if p is False: return False
            if p is None: result = None
        return result
    p, q = args
    if op == '>>':
        return pl_true(~p | q, model)
    elif op == '<<':
        return pl_true(p | ~q, model)
    pt = pl_true(p, model)
    if pt is None: return None
    qt = pl_true(q, model)
    if qt is None: return None
    if op == '<=>':
        return pt == qt
    elif op == '^':
        return pt != qt
    else:
        raise ValueError, "illegal operator in logic expression" + str(exp)

#______________________________________________________________________________

## Convert to Conjunctive Normal Form (CNF)

def to_cnf(s):
    """Convert a propositional logical sentence s to conjunctive normal form.
    That is, to the form ((A | ~B | ...) & (B | C | ...) & ...) [p. 253]
    >>> to_cnf("~(B|C)")
    (~B & ~C)
    >>> to_cnf("B <=> (P1|P2)")
    ((~P1 | B) & (~P2 | B) & (P1 | P2 | ~B))
    >>> to_cnf("a | (b & c) | d")
    ((b | a | d) & (c | a | d))
    >>> to_cnf("A & (B | (D & E))")
    (A & (D | B) & (E | B))
    >>> to_cnf("A | (B | (C | (D & E)))")
    ((D | A | B | C) & (E | A | B | C))
    """
    if isinstance(s, str): s = expr(s)
    s = eliminate_implications(s) # Steps 1, 2 from p. 253
    s = move_not_inwards(s) # Step 3
    return distribute_and_over_or(s) # Step 4

def eliminate_implications(s):
    """Change >>, <<, and <=> into &, |, and ~. That is, return an Expr
    that is equivalent to s, but has only &, |, and ~ as logical operators.
    >>> eliminate_implications(A >> (~B << C))
    ((~B | ~C) | ~A)
    >>> eliminate_implications(A ^ B)
    ((A & ~B) | (~A & B))
    """
    if not s.args or is_symbol(s.op): return s     ## (Atoms are unchanged.)
    args = map(eliminate_implications, s.args)
    a, b = args[0], args[-1]
    if s.op == '>>':
        return (b | ~a)
    elif s.op == '<<':
        return (a | ~b)
    elif s.op == '<=>':
        return (a | ~b) & (b | ~a)
    elif s.op == '^':
        assert len(args) == 2   ## TODO: relax this restriction
        return (a & ~b) | (~a & b)
    else:
        assert s.op in ('&', '|', '~')
        return Expr(s.op, *args)

def move_not_inwards(s):
    """Rewrite sentence s by moving negation sign inward.
    >>> move_not_inwards(~(A | B))
    (~A & ~B)
    >>> move_not_inwards(~(A & B))
    (~A | ~B)
    >>> move_not_inwards(~(~(A | ~B) | ~~C))
    ((A | ~B) & ~C)
    """
    if s.op == '~':
        NOT = lambda b: move_not_inwards(~b)
        a = s.args[0]
        if a.op == '~': return move_not_inwards(a.args[0]) # ~~A ==> A
        if a.op =='&': return associate('|', map(NOT, a.args))
        if a.op =='|': return associate('&', map(NOT, a.args))
        return s
    elif is_symbol(s.op) or not s.args:
        return s
    else:
        return Expr(s.op, *map(move_not_inwards, s.args))

def distribute_and_over_or(s):
    """Given a sentence s consisting of conjunctions and disjunctions
    of literals, return an equivalent sentence in CNF.
    >>> distribute_and_over_or((A & B) | C)
    ((A | C) & (B | C))
    """
    if s.op == '|':
        s = associate('|', s.args)
        if s.op != '|':
            return distribute_and_over_or(s)
        if len(s.args) == 0:
            return FALSE
        if len(s.args) == 1:
            return distribute_and_over_or(s.args[0])
        conj = find_if((lambda d: d.op == '&'), s.args)
        if not conj:
            return s
        others = [a for a in s.args if a is not conj]
        rest = associate('|', others)
        return associate('&', [distribute_and_over_or(c|rest)
                               for c in conj.args])
    elif s.op == '&':
        return associate('&', map(distribute_and_over_or, s.args))
    else:
        return s

def associate(op, args):
    """Given an associative op, return an expression with the same
    meaning as Expr(op, *args), but flattened -- that is, with nested
    instances of the same op promoted to the top level.
    >>> associate('&', [(A&B),(B|C),(B&C)])
    (A & B & (B | C) & B & C)
    >>> associate('|', [A|(B|(C|(A&B)))])
    (A | B | C | (A & B))
    """
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)

_op_identity = {'&':TRUE, '|':FALSE, '+':ZERO, '*':ONE}

def dissociate(op, args):
    """Given an associative op, return a flattened list result such
    that Expr(op, *result) means the same as Expr(op, *args)."""
    result = []
    def collect(subargs):
        for arg in subargs:
            if arg.op == op: collect(arg.args)
            else: result.append(arg)
    collect(args)
    return result

def conjuncts(s):
    """Return a list of the conjuncts in the sentence s.
    >>> conjuncts(A & B)
    [A, B]
    >>> conjuncts(A | B)
    [(A | B)]
    """
    return dissociate('&', [s])

def disjuncts(s):
    """Return a list of the disjuncts in the sentence s.
    >>> disjuncts(A | B)
    [A, B]
    >>> disjuncts(A & B)
    [(A & B)]
    """
    return dissociate('|', [s])

#______________________________________________________________________________

def pl_resolution(KB, alpha):
    "Propositional-logic resolution: say if alpha follows from KB. [Fig. 7.12]"
    clauses = KB.clauses + conjuncts(to_cnf(~alpha))
    new = set()
    while True:
        n = len(clauses)
        pairs = [(clauses[i], clauses[j])
                 for i in range(n) for j in range(i+1, n)]
        for (ci, cj) in pairs:
            resolvents = pl_resolve(ci, cj)
            if FALSE in resolvents: return True
            new = new.union(set(resolvents))
        if new.issubset(set(clauses)): return False
        for c in new:
            if c not in clauses: clauses.append(c)

def pl_resolve(ci, cj):
    """Return all clauses that can be obtained by resolving clauses ci and cj.
    >>> for res in pl_resolve(to_cnf(A|B|C), to_cnf(~B|~C|F)):
    ...    ppset(disjuncts(res))
    set([A, C, F, ~C])
    set([A, B, F, ~B])
    """
    clauses = []
    for di in disjuncts(ci):
        for dj in disjuncts(cj):
            if di == ~dj or ~di == dj:
                dnew = unique(removeall(di, disjuncts(ci)) +
                              removeall(dj, disjuncts(cj)))
                clauses.append(associate('|', dnew))
    return clauses

#______________________________________________________________________________
#______________________________________________________________________________

def unify(x, y, s):
    """Unify expressions x,y with substitution s; return a substitution that
    would make x,y equal, or None if x,y can not unify. x and y can be
    variables (e.g. Expr('x')), constants, lists, or Exprs. [Fig. 9.1]
    >>> ppsubst(unify(x + y, y + C, {}))
    {x: y, y: C}
    """
    if s is None:
        return None
    elif x == y:
        return s
    elif is_variable(x):
        return unify_var(x, y, s)
    elif is_variable(y):
        return unify_var(y, x, s)
    elif isinstance(x, Expr) and isinstance(y, Expr):
        return unify(x.args, y.args, unify(x.op, y.op, s))
    elif isinstance(x, str) or isinstance(y, str):
        return None
    elif issequence(x) and issequence(y) and len(x) == len(y):
        if not x: return s
        return unify(x[1:], y[1:], unify(x[0], y[0], s))
    else:
        return None

def is_variable(x):
    "A variable is an Expr with no args and a lowercase symbol as the op."
    return isinstance(x, Expr) and not x.args and is_var_symbol(x.op)

def unify_var(var, x, s):
    if var in s:
        return unify(s[var], x, s)
    elif occur_check(var, x, s):
        return None
    else:
        return extend(s, var, x)

def occur_check(var, x, s):
    """Return true if variable var occurs anywhere in x
    (or in subst(s, x), if s has a binding for x)."""
    if var == x:
        return True
    elif is_variable(x) and x in s:
        return occur_check(var, s[x], s)
    elif isinstance(x, Expr):
        return (occur_check(var, x.op, s) or
                occur_check(var, x.args, s))
    elif isinstance(x, (list, tuple)):
        return some(lambda element: occur_check(var, element, s), x)
    else:
        return False

def extend(s, var, val):
    """Copy the substitution s and extend it by setting var to val;
    return copy.
    >>> ppsubst(extend({x: 1}, y, 2))
    {x: 1, y: 2}
    """
    s2 = s.copy()
    s2[var] = val
    return s2

def subst(s, x):
    """Substitute the substitution s into the expression x.
    >>> subst({x: 42, y:0}, F(x) + y)
    (F(42) + 0)
    """
    if isinstance(x, list):
        return [subst(s, xi) for xi in x]
    elif isinstance(x, tuple):
        return tuple([subst(s, xi) for xi in x])
    elif not isinstance(x, Expr):
        return x
    elif is_var_symbol(x.op):
        return s.get(x, x)
    else:
        return Expr(x.op, *[subst(s, arg) for arg in x.args])


def fol_fc_ask(KB, alpha):
    """Inefficient forward chaining for first-order logic. [Fig. 9.3]
    KB is a FolKB and alpha must be an atomic sentence."""
    while True:
        new = {}
        for r in KB.clauses:
            ps, q = parse_definite_clause(standardize_variables(r))
            raise NotImplementedError

def standardize_variables(sentence, dic=None):
    """Replace all the variables in sentence with new variables.
    >>> e = expr('F(a, b, c) & G(c, A, 23)')
    >>> len(variables(standardize_variables(e)))
    3
    >>> variables(e).intersection(variables(standardize_variables(e)))
    set([])
    >>> is_variable(standardize_variables(expr('x')))
    True
    """
    if dic is None: dic = {}
    if not isinstance(sentence, Expr):
        return sentence
    elif is_var_symbol(sentence.op):
        if sentence in dic:
            return dic[sentence]
        else:
            v = Expr('v_%d' % standardize_variables.counter.next())
            dic[sentence] = v
            return v
    else:
        return Expr(sentence.op,
                    *[standardize_variables(a, dic) for a in sentence.args])

standardize_variables.counter = itertools.count()

#______________________________________________________________________________

class FolKB(KB):
    def __init__(self, initial_clauses=[]):
        self.clauses = [] # inefficient: no indexing
        for clause in initial_clauses:
            self.tell(clause)

    def tell(self, sentence):
        if is_definite_clause(sentence):
            self.clauses.append(sentence)
        else:
            raise Exception("Not a definite clause: %s" % sentence)

    def ask_generator(self, query):
        return fol_bc_ask(self, query)

    def retract(self, sentence):
        self.clauses.remove(sentence)

    def fetch_rules_for_goal(self, goal):
        return self.clauses

def test_ask(query, kb=None):
    q = expr(query)
    vars = variables(q)
    answers = fol_bc_ask(kb or test_kb, q)
    return sorted([pretty(dict((x, v) for x, v in a.items() if x in vars))
                   for a in answers],
                  key=repr)

test_kb = FolKB(
    map(expr, ['Farmer(Mac)',
               'Rabbit(Pete)',
               'Mother(MrsMac, Mac)',
               'Mother(MrsRabbit, Pete)',
               '(Rabbit(r) & Farmer(f)) ==> Hates(f, r)',
               '(Mother(m, c)) ==> Loves(m, c)',
               '(Mother(m, r) & Rabbit(r)) ==> Rabbit(m)',
               '(Farmer(f)) ==> Human(f)',
               # Note that this order of conjuncts
               # would result in infinite recursion:
               #'(Human(h) & Mother(m, h)) ==> Human(m)'
               '(Mother(m, h) & Human(h)) ==> Human(m)'
               ])
)

crime_kb = FolKB(
  map(expr,
    ['(American(x) & Weapon(y) & Sells(x, y, z) & Hostile(z)) ==> Criminal(x)',
     'Owns(Nono, M1)',
     'Missile(M1)',
     '(Missile(x) & Owns(Nono, x)) ==> Sells(West, x, Nono)',
     'Missile(x) ==> Weapon(x)',
     'Enemy(x, America) ==> Hostile(x)',
     'American(West)',
     'Enemy(Nono, America)'
     ])
)

def fol_bc_ask(KB, query):
    """A simple backward-chaining algorithm for first-order logic. [Fig. 9.6]
    KB should be an instance of FolKB, and goals a list of literals.
    >>> test_ask('Farmer(x)')
    ['{x: Mac}']
    >>> test_ask('Human(x)')
    ['{x: Mac}', '{x: MrsMac}']
    >>> test_ask('Hates(x, y)')
    ['{x: Mac, y: MrsRabbit}', '{x: Mac, y: Pete}']
    >>> test_ask('Loves(x, y)')
    ['{x: MrsMac, y: Mac}', '{x: MrsRabbit, y: Pete}']
    >>> test_ask('Rabbit(x)')
    ['{x: MrsRabbit}', '{x: Pete}']
    >>> test_ask('Criminal(x)', crime_kb)
    ['{x: West}']
    """
    return fol_bc_or(KB, query, {})

entailedlist = []
def isloopcheck(pushfact):
    #global entailedlist
    if pushfact not in entailedlist:
        entailedlist.append(pushfact)
        return False
    if pushfact in entailedlist:
        return True

def isFact(alhs):
     for i in alhs.args:
        if is_variable(i):
            return False
     return True


def fol_bc_or(KB, goal, theta):
    for rule in KB.fetch_rules_for_goal(goal):
        lhs, rhs = parse_definite_clause(standardize_variables(rule))
        temp_theta = unify(rhs, goal, theta)
        if temp_theta:
            newlhs =[]
            for i in lhs :
                 lhssubs = subst(temp_theta,i)
                 if isFact(lhssubs):
                        if not isloopcheck(lhssubs):
                            newlhs.append(i)
            lhs = newlhs

        for theta1 in fol_bc_and(KB, lhs, unify(rhs, goal, theta)):
            yield theta1

def fol_bc_and(KB, goals, theta):
    if theta is None:
        pass
    elif not goals:
        yield theta
    else:
        first, rest = goals[0], goals[1:]
        for theta1 in fol_bc_or(KB, subst(theta, first), theta):
            for theta2 in fol_bc_and(KB, rest, theta1):
                yield theta2

#______________________________________________________________________________

# Example application (not in the book).
# You can use the Expr class to do symbolic differentiation.  This used to be
# a part of AI; now it is considered a separate field, Symbolic Algebra.

def diff(y, x):
    """Return the symbolic derivative, dy/dx, as an Expr.
    However, you probably want to simplify the results with simp.
    >>> diff(x * x, x)
    ((x * 1) + (x * 1))
    >>> simp(diff(x * x, x))
    (2 * x)
    """
    if y == x: return ONE
    elif not y.args: return ZERO
    else:
        u, op, v = y.args[0], y.op, y.args[-1]
        if op == '+': return diff(u, x) + diff(v, x)
        elif op == '-' and len(args) == 1: return -diff(u, x)
        elif op == '-': return diff(u, x) - diff(v, x)
        elif op == '*': return u * diff(v, x) + v * diff(u, x)
        elif op == '/': return (v*diff(u, x) - u*diff(v, x)) / (v * v)
        elif op == '**' and isnumber(x.op):
            return (v * u ** (v - 1) * diff(u, x))
        elif op == '**': return (v * u ** (v - 1) * diff(u, x)
                                 + u ** v * Expr('log')(u) * diff(v, x))
        elif op == 'log': return diff(u, x) / u
        else: raise ValueError("Unknown op: %s in diff(%s, %s)" % (op, y, x))

def simp(x):
    if not x.args: return x
    args = map(simp, x.args)
    u, op, v = args[0], x.op, args[-1]
    if op == '+':
        if v == ZERO: return u
        if u == ZERO: return v
        if u == v: return TWO * u
        if u == -v or v == -u: return ZERO
    elif op == '-' and len(args) == 1:
        if u.op == '-' and len(u.args) == 1: return u.args[0] ## --y ==> y
    elif op == '-':
        if v == ZERO: return u
        if u == ZERO: return -v
        if u == v: return ZERO
        if u == -v or v == -u: return ZERO
    elif op == '*':
        if u == ZERO or v == ZERO: return ZERO
        if u == ONE: return v
        if v == ONE: return u
        if u == v: return u ** 2
    elif op == '/':
        if u == ZERO: return ZERO
        if v == ZERO: return Expr('Undefined')
        if u == v: return ONE
        if u == -v or v == -u: return ZERO
    elif op == '**':
        if u == ZERO: return ZERO
        if v == ZERO: return ONE
        if u == ONE: return ONE
        if v == ONE: return u
    elif op == 'log':
        if u == ONE: return ZERO
    else: raise ValueError("Unknown op: " + op)
    ## If we fall through to here, we can not simplify further
    return Expr(op, *args)

def d(y, x):
    "Differentiate and then simplify."
    return simp(diff(y, x))

#_______________________________________________________________________________

# Utilities for doctest cases
# These functions print their arguments in a standard order
# to compensate for the random order in the standard representation

def pretty(x):
    t = type(x)
    if t is dict:  return pretty_dict(x)
    elif t is set: return pretty_set(x)
    else:          return repr(x)

def pretty_dict(d):
    """Return dictionary d's repr but with the items sorted.
    >>> pretty_dict({'m': 'M', 'a': 'A', 'r': 'R', 'k': 'K'})
    "{'a': 'A', 'k': 'K', 'm': 'M', 'r': 'R'}"
    >>> pretty_dict({z: C, y: B, x: A})
    '{x: A, y: B, z: C}'
    """
    return '{%s}' % ', '.join('%r: %r' % (k, v)
                              for k, v in sorted(d.items(), key=repr))

def pretty_set(s):
    """Return set s's repr but with the items sorted.
    >>> pretty_set(set(['A', 'Q', 'F', 'K', 'Y', 'B']))
    "set(['A', 'B', 'F', 'K', 'Q', 'Y'])"
    >>> pretty_set(set([z, y, x]))
    'set([x, y, z])'
    """
    return 'set(%r)' % sorted(s, key=repr)

def pp(x):
    print pretty(x)

def ppsubst(s):
    """Pretty-print substitution s"""
    ppdict(s)

def ppdict(d):
    print pretty_dict(d)

def ppset(s):
    print pretty_set(s)

#________________________________________________________________________

class logiTest:

    f = open('C:\\Users\\Shivankur Kapoor\\Desktop\\USC\\SEM 1\\561 - AI\\Assignment 3\\input_1.txt','r+')
    numq = f.readline()
    qlist = []
    for i in range(1,int(numq)+1):
        s = f.readline()
        s = s.replace(",",", ")[0:]
        s = s.replace("~","Not")[0:]
        qlist.append(s.rstrip('\n'))
#print qlist

    numkb = f.readline()
    kb = []
    for i in range(1,int(numkb)+1):
        s = f.readline()
        mystr = "=>"
        if mystr in s:
            index = s.find(mystr)
            s = "(" + s[0:index-1] + ") " + s[index:]
        s = s.replace(",",", ")[0:]
        s = s.replace("=>","==>")[0:]
        s = s.replace("^","&")[0:]
        s = s.replace("~","Not")[0:]
        kb.append(s.rstrip('\n'))
#print kb

    crime_kb11 = FolKB(
     map(expr,kb)
    )

    for i in qlist:
        mylst1 = fol_bc_ask(crime_kb11,expr(i))
        lst = list(mylst1)
        if len(lst) > 0 :
            print "TRUE"
        else :
            print "FALSE"