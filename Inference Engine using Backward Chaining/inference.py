#-------------------------------------------------------------------------------
# Name:        inference
# Purpose:     AI Assignment
#
# Author:      Shivankur Kapoor
#
# Created:      11/1/2015
# Copyright:   (c) Shivankur Kapoor
# Licence:     <Open Source>
#-------------------------------------------------------------------------------

from __future__ import generators
import itertools, re
import operator, math, random, copy, sys, os.path, bisect, re
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
# UTILITY FUNCTIONS

try: reversed
except NameError:
    def reversed(seq):
        if hasattr(seq, 'keys'):
            raise TypeError("ERROR")
        i = len(seq)
        while i > 0:
            i -= 1
            yield seq[i]

try: sorted
except NameError:
    def sorted(seq, cmp=None, key=None, reverse=False):
        seq2 = copy.copy(seq)
        if key:
            if cmp == None:
                cmp = __builtins__.cmp
            seq2.sort(lambda x,y: cmp(key(x), key(y)))
        else:
            if cmp == None:
                seq2.sort()
            else:
                seq2.sort(cmp)
        if reverse:
            seq2.reverse()
        return seq2



try:
    set, frozenset
except NameError:
    try:
        import sets
        set, frozenset = sets.Set, sets.ImmutableSet
    except (NameError, ImportError):
        class BaseSet:
            def __init__(self, elements=[]):
                self.dict = {}
                for e in elements:
                    self.dict[e] = 1

            def __len__(self):
                return len(self.dict)

            def __iter__(self):
                for e in self.dict:
                    yield e

            def __contains__(self, element):
                return element in self.dict

            def difference(self, other):
                return type(self)([e for e in self.dict if e not in other])

            def symmetric_difference(self, other):
                return type(self)([e for e in self.dict if e not in other] +
                                  [e for e in other if e not in self.dict])

            def copy(self):
                return type(self)(self.dict)

            def __repr__(self):
                elements = ", ".join(map(str, self.dict))
                return "%s([%s])" % (type(self).__name__, elements)

            __le__ = issubset
            __ge__ = issuperset
            __or__ = union
            __and__ = intersection
            __sub__ = difference
            __xor__ = symmetric_difference

infinity = 1.0e400

def Dict(**entries):
      return entries

class DefaultDict(dict):
    def __init__(self, default):
        self.default = default

    def __getitem__(self, key):
        if key in self: return self.get(key)
        return self.setdefault(key, copy.deepcopy(self.default))

    def __copy__(self):
        copy = DefaultDict(self.default)
        copy.update(self)
        return copy

class Struct:
    def __init__(self, **entries):
        self.__dict__.update(entries)

    def __cmp__(self, other):
        if isinstance(other, Struct):
            return cmp(self.__dict__, other.__dict__)
        else:
            return cmp(self.__dict__, other)

    def __repr__(self):
        args = ['%s=%s' % (k, repr(v)) for (k, v) in vars(self).items()]
        return 'Struct(%s)' % ', '.join(sorted(args))


def update(x, **entries):
    if isinstance(x, dict):
        x.update(entries)
    else:
        x.__dict__.update(entries)
    return x

def removeall(item, seq):
    if isinstance(seq, str):
        return seq.replace(item, '')
    else:
        return [x for x in seq if x != item]

def unique(seq):
    return list(set(seq))

def product(numbers):
    return reduce(operator.mul, numbers, 1)

def count_if(predicate, seq):
    f = lambda count, x: count + (not not predicate(x))
    return reduce(f, seq, 0)

def find_if(predicate, seq):
    for x in seq:
        if predicate(x): return x
    return None

def every(predicate, seq):
    for x in seq:
        if not predicate(x): return False
    return True

def some(predicate, seq):
    for x in seq:
        px = predicate(x)
        if px: return px
    return False

def isin(elt, seq):
    for x in seq:
        if elt is x: return True
    return False

def num_or_str(x):
    if isnumber(x): return x
    try:
        return int(x)
    except ValueError:
        try:
            return float(x)
        except ValueError:
            return str(x).strip()


def printf(format, *args):
    sys.stdout.write(str(format) % args)
    return if_(args, lambda: args[-1], lambda: format)

def caller(n=1):
    import inspect
    return inspect.getouterframes(inspect.currentframe())[n][3]

def if_(test, result, alternative):
    if test:
        if callable(result): return result()
        return result
    else:
        if callable(alternative): return alternative()
        return alternative

def name(object):
    return (getattr(object, 'name', 0) or getattr(object, '__name__', 0)
            or getattr(getattr(object, '__class__', 0), '__name__', 0)
            or str(object))

def isnumber(x):
    return hasattr(x, '__int__')

def issequence(x):
    return hasattr(x, '__getitem__')

#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
# KNOWLWDGE IS DEFINED BELOW

class KB:

    def __init__(self, sentence=None):
        abstract

    def tell(self, sentence):
        "Add the sentence to the KB."
        abstract

    def ask(self, query):
        for result in self.ask_generator(query):
            return result
        return False

#______________________________________________________________________________
# LOGIC FOR PARSING OF KNOWLEDGE BASE
class Expr:

    def __init__(self, op, *args):
        assert isinstance(op, str) or (isnumber(op) and not args)
        self.op = num_or_str(op)
        self.args = map(expr, args) ## Coerce args to Exprs

    def __call__(self, *args):
        assert is_symbol(self.op) and not self.args
        return Expr(self.op, *args)

    def __repr__(self):
        if not self.args:         # Constant or proposition with arity 0
            return str(self.op)
        elif is_symbol(self.op):  # Functional or propositional operator
            return '%s(%s)' % (self.op, ', '.join(map(repr, self.args)))
        elif len(self.args) == 1: # Prefix operator
            return self.op + repr(self.args[0])
        else:                     # Infix operator
            return '(%s)' % (' '+self.op+' ').join(map(repr, self.args))

    def __eq__(self, other):
        return (other is self) or (isinstance(other, Expr)
            and self.op == other.op and self.args == other.args)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.op) ^ hash(tuple(self.args))
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
    return is_symbol(s) and s[0].isupper() and s != 'TRUE' and s != 'FALSE'

def variables(s):
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
    if is_symbol(s.op):
        return True
    elif s.op == '>>':
        antecedent, consequent = s.args
        return (is_symbol(consequent.op)
                and every(lambda arg: is_symbol(arg.op), conjuncts(antecedent)))
    else:
        return False

def parse_definite_clause(s):
    assert is_definite_clause(s)
    if is_symbol(s.op):
        return [], s
    else:
        antecedent, consequent = s.args
        return conjuncts(antecedent), consequent

TRUE, FALSE, ZERO, ONE, TWO = map(Expr, ['TRUE', 'FALSE', 0, 1, 2])
A, B, C, D, E, F, G, P, Q, x, y, z  = map(Expr, 'ABCDEFGPQxyz')

#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________

def prop_symbols(x):
    "Return a list of all propositional symbols in x."
    if not isinstance(x, Expr):
        return []
    elif is_prop_symbol(x.op):
        return [x]
    else:
        return list(set(symbol for arg in x.args
                        for symbol in prop_symbols(arg)))

def pl_true(exp, model={}):
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
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________

def associate(op, args):
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)

_op_identity = {'&':TRUE, '|':FALSE, '+':ZERO, '*':ONE}

def dissociate(op, args):
    result = []
    def collect(subargs):
        for arg in subargs:
            if arg.op == op: collect(arg.args)
            else: result.append(arg)
    collect(args)
    return result

def conjuncts(s):
    return dissociate('&', [s])

def disjuncts(s):
    return dissociate('|', [s])

#______________________________________________________________________________
#______________________________________________________________________________
# LOGIC FOR UNIFICATION

def unify(x, y, s):
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
    s2 = s.copy()
    s2[var] = val
    return s2

def subst(s, x):
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


def standardize_variables(sentence, dic=None):
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
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
# MAIN LOGIC FOR BACKWARD CHAINING SYSTEM

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

    def fetch_rules_for_goal(self, goal):
        return self.clauses

#

def isloopcheck(pushfact):
    #global entailedlist
    if pushfact not in entailedlist:
        entailedlist.append(pushfact)
        return False
    if pushfact in entailedlist:
        return True

def loopDetection(loopList,goal):
    for i in loopList:
       listofArgs1 = i.args
       listofArgs2 = goal.args
       length = len(listofArgs1)
       if i.op== goal.op:
         for a1,a2 in itertools.izip(listofArgs1,listofArgs2):
             if is_variable(a1) and is_variable(a2):
                length=length-1
                continue
             if is_variable(a1) or is_variable(a2):
                break
             if a1==a2:
                length=length-1
                continue
             else:
                break

       if length==0:
        return True
    return False



def fol_bc_ask(KB, query):
    return fol_bc_or(KB, query, {},[])


def isFact(alhs):
     for i in alhs.args:
        if is_variable(i):
            return False
     return True

def isFactinKB(lhssubs,KB):
     for rule in KB.fetch_rules_for_goal(lhssubs):
         lhs, rhs = parse_definite_clause(standardize_variables(rule))
         if not lhs and isFact(rhs):
             if rhs == lhssubs:
                return True
     return False


def fol_bc_or(KB, goal, theta,loopList):
  #  if unify(rhs, goal, theta) and not isFact(rhs):
     a1=1
     if loopDetection(loopList,goal):
         return
     else:
         loopList.append(goal)
     for rule in KB.fetch_rules_for_goal(goal):
        lhs, rhs = parse_definite_clause(standardize_variables(rule))
        for theta1 in fol_bc_and(loopList,KB, lhs, unify(rhs, goal, theta)):
            yield theta1

def fol_bc_and(loopList,KB, goals, theta):
    a2 =0
    if theta is None:
        pass
    elif not goals:
        yield theta
    else:
        first, rest = goals[0], goals[1:]
        loopList1 = list(loopList)
        for theta1 in fol_bc_or(KB, subst(theta, first), theta,loopList1):
            for theta2 in fol_bc_and(loopList,KB, rest, theta1):
                yield theta2

#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
#______________________________________________________________________________
# FOR PRINTING PURPOSE

def pretty(x):
    t = type(x)
    if t is dict:  return pretty_dict(x)
    elif t is set: return pretty_set(x)
    else:          return repr(x)

def pretty_dict(d):
    return '{%s}' % ', '.join('%r: %r' % (k, v)
                              for k, v in sorted(d.items(), key=repr))

def pretty_set(s):
    return 'set(%r)' % sorted(s, key=repr)

def pp(x):
    print pretty(x)

def ppsubst(s):
    ppdict(s)

def ppdict(d):
    print pretty_dict(d)

def ppset(s):
    print pretty_set(s)

#________________________________________________________________________

class inferenceTest:

    #f = open('C:\\Users\\Shivankur Kapoor\\Desktop\\USC\\SEM 1\\561 - AI\\Assignment 3\\input_1.txt','r+')
    fr = open(sys.argv[1],'r+')
    numOfQueries = fr.readline()
    qlist = []
    for i in range(1,int(numOfQueries)+1):
        s = fr.readline()
        s = s.replace(",",", ")[0:]
        s = s.replace("~","Not")[0:]
        qlist.append(s.rstrip('\n'))
#print qlist

    sizeOfKB = fr.readline()
    kb = []
    for i in range(1,int(sizeOfKB)+1):
        s = fr.readline()
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
    fw = open('C:\\Users\\Shivankur Kapoor\\Desktop\\USC\\SEM 1\\561 - AI\Assignment 3\output.txt','w')
    new_kb = FolKB(
     map(expr,kb)
    )

    for i in qlist:
        mylst1 = fol_bc_ask(new_kb,expr(i))
        lst = list(mylst1)
        if len(lst) > 0 :
            fw.write('TRUE\n')
            print "TRUE"
        else :
            fw.write('FALSE\n')
            print "FALSE"
    fr.close()
    fw.close()
