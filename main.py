import numpy as np

def is_prime(x):
    for d in range(2,int(x**.5)+1):
        if x%d==0:
            return False
    return True

def is_generator(g,p=223,debug=False):
    s = set([1])
    ga = 1
    if debug: print(0,ga)
    for i in range(p-2):
        ga = ga * g % p
        if debug: print(i+1,ga)
        if ga in s: return False
        s.add(ga)
    return True

def gens(p): return [x for x in range(1,p) if is_generator(x,p)]
all_primes_under = lambda maxp: list(filter(is_prime, range(2,maxp)))

def get_all_generators(n): return list(filter(lambda x: is_generator(x,n), range(n)))
def compose(f,g): return lambda x:f(g(x))
is_cyclic = compose(any, get_all_generators)
get_generator = compose(lambda x:x[0], get_all_generators)

assert(all(map(is_cyclic, all_primes_under(100))))

def discrete_logarithm(h,p=223,g=None,debug=False):
    if not g:
        g = get_generator(p)
    ga = 1
    if ga == h: return 0
    if debug: print(0,ga)
    for i in range(p-2):
        if ga == h: return i
        ga = ga * g % p
        if debug: print(i+1,ga)
    return 0

def eqmod(a,b,m): return abs(a-b)%m == 0

def hidden_addition():
    p = 223
    g = get_generator(p)
    E = lambda x: (g**x)%p
    def prover(x,y): # prover -- that has x,y st x+y = 7
        return E(x), E(y), x+y
    def verifier(ex,ey,xpy): # verifier
        exy = ex * ey
        assert eqmod(exy, E(xpy), p)
    ex,ey,xpy = prover(3,4)
    verifier(ex,ey,xpy)

def hidden_linear_comb():
    p = 223
    g = get_generator(p)
    E = lambda x: (g**x)%p
    a,b = 2,5
    def prover(x,y): # prover -- that has x,y st x+y = 7
        return E(x), E(y), (a*x+b*y % p)
    def verifier(ex,ey,comb): # verifier
        exy = (ex**a * ey**b) % p
        assert eqmod(exy, E(comb), p)
    ex,ey,comb = prover(3,4) #secret x and y
    verifier(ex,ey,comb)

def fold(op, lst, init):
    accum = init
    for x in lst:
        accum = op(accum, x)
    return accum

def mult(lst): return fold(lambda x,y:x*y, lst, 1)

def hidden_nary_linear_comb():
    p = 223
    g = get_generator(p)
    E = lambda x: (g**x)%p
    coeffs = [2,5,3]
    mult = lambda lst: fold(lambda x,y:(x*y)%p, lst, 1)
    def prover(secret_vars): # prover -- that has x,y st x+y = 7
        comb = sum(map(lambda x:x[0]*x[1]%p, zip(coeffs, secret_vars)))
        return list(map(E,secret_vars)), comb
    def verifier(es,comb): # verifier
        Ecomb = mult(map(lambda x:(x[0]**x[1])%p, zip(es,coeffs)))
        assert eqmod(Ecomb, E(comb), p)
    es, comb = prover([3,4,1])
    verifier(es,comb)

def unforced_blind_polynomial_eval():
    p = 223
    g = get_generator(p)
    E = lambda x: (g**x)%p
    degree = 5
    def alice(secret_point): #doesn't know polynomial coeffs
        return list(map(lambda d: E((secret_point**d)%p), range(degree)))
    def bob(secret_coeffs, powers): #doesn't know point
        return E(sum(map(lambda x:x[0]*x[1]%p, zip(secret_coeffs, powers))))
    es = alice(3)
    EPs = bob([3,0,2,1,2], es)
    return EPs

def kc_test():
    p = 223
    g = get_generator(p)
    a = 3
    def bob_scope(alpha):
        def bob_1():
            return (a%p,(a*alpha)%p)
        def bob_2(ga, gb):
            assert(eqmod(alpha*ga, gb, p))
        return bob_1, bob_2
    def alice(a,b,gamma):
        return (gamma*a)%p, (gamma*b)%p
    bob_1, bob_2 = bob_scope(3)
    a,b = bob_1()
    ga,gb = alice(a,b,5)
    bob_2(ga,gb)

def extended_kc_test():
    p = 223
    g = get_generator(p)
    a_vals = [3,6,1]
    def linear_comb(coeffs, xs):
        return sum(map(lambda x:x[0]*x[1]%p, zip(coeffs, xs)))
    def bob_scope(alpha):
        def bob_1():
            return list(map(lambda a:(a*alpha)%p, a_vals))
        def bob_2(ga, gb):
            assert(eqmod(alpha*ga, gb, p))
        return bob_1, bob_2
    def alice(b_vals,gamma):
        coeffs = [2,1,1]
        out_a = linear_comb(coeffs, a_vals)
        out_b = linear_comb(coeffs, b_vals)
        return out_a, out_b
    bob_1, bob_2 = bob_scope(3)
    b_vals = bob_1()
    out_a,out_b = alice(b_vals,5)
    bob_2(out_a, out_b)

def verifiable_blind_polynomial_eval():
    p = 223
    g = get_generator(p)
    E = lambda x: (g*x)%p
    degree = 5
    def linear_comb(coeffs, xs):
        return sum(map(lambda x:x[0]*x[1]%p, zip(coeffs, xs)))
    def bob_fxns(point, alpha): #doesn't know polynomial coeffs
        def bob_1():
            a_vals = list(map(lambda d: E((point**d)%p), range(degree)))
            b_vals = list(map(lambda a: (alpha*a)%p, a_vals))
            return a_vals, b_vals
        def bob_2(a,b):
            assert eqmod(alpha*a,b,p)
        return bob_1, bob_2
    def alice(a_vals, b_vals, coeffs): #doesn't know point
        a = linear_comb(coeffs, a_vals)
        b = linear_comb(coeffs, b_vals)
        return a, b
    bob_1,bob_2 = bob_fxns(3,4)
    a_vals, b_vals = bob_1()
    result, b_out = alice(a_vals, b_vals, [3,0,2,1,2])
    bob_2(result, b_out)
    return result

def poly_plus(p1,p2):
    l1, l2=p1.shape[0], p2.shape[0]
    diff = l2 - l1
    if diff == 0:
        return p1 + p2
    elif diff > 0:
        return np.concatenate([p1,np.zeros(diff)]) + p2
    else:
        return p1 + np.concatenate([p2,np.zeros(-diff)])
def poly_times(p1,p2): return np.convolve(p1,p2)
def poly_apply(p,x):
    if p.shape[0] == 1: return p[0]
    return p[0] + x*poly_apply(p[1:],x)

def interpolate(xs,ys):
    p = np.array([])
    for (x_j,y_j) in zip(xs,ys):
        l_j = np.array([1])
        for x in xs:
            if x != x_j:
                l_j = poly_times(np.array([-x,1]),l_j) / (x_j-x)
        p = poly_plus(p, y_j*l_j)
    return p

class C:
    #C("+",C(4),C(3)).eval() <- 7
    #C("*",C(4),C(3)).eval() <- 12
    def __init__(self, data, left=None, right=None):
        self.left = left
        self.right = right
        self.data = data
    def print_tree(self):
        if self.left: print(self.left)
        print(self.data)
        if self.right: print(self.right)
    def eval(self):
        if isinstance(self.data,int):
            return self.data
        if self.data == "+": return self.left.eval() + self.right.eval()
        return self.left.eval() * self.right.eval()

# todo -- assign field numbers to multiplication points
#  interpolate to get polynomial representing circuit
#  add elliptical hiding for multiplication algorithm
#  assemble pieces into pinocchio protocol
