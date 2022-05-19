

class Diamond:
    """The main diamond-shaped commutative diagram we are working in."""

    def __init__(self, f, g, m, N):
        assert f(m) % N == 0
        assert g(m) % N == 0
        self.left = NumberField(f, 'x')
        self.right = NumberField(g, 'x')
        self.bottom = Integers(N)
        self.m = m
        self.N = N

    def le(self, f):
        return f(self.left.gen())

    def re(self, f):
        return f(self.right.gen())

    def lp(self, a):
        return self.bottom(a.polynomial()(self.m))

    def rp(self, a):
        return self.bottom(a.polynomial()(self.m))

class SmoothElement:
    """A number field element together with all prime ideal factor valuations."""

    def __init__(self, element, p_valuations):
        self.element = element
        self.p_valuations = p_valuations

    def __repr__(self) -> str:
        return str(self.element)

def gen_factor_basis(B, K):
    result = {}
    f = K.gen().minpoly()
    poly_ring = PolynomialRing(ZZ, ['X'])
    for p in Primes():
        if p > B:
            return result
        # either f mod p splits, or not...
        factorization = factor(f.change_ring(GF(p)))
        result[p] = [
            K.ideal([p, poly_ring(factorization[i][0])(K.gen())]) for i in range(len(factorization))
        ]
        
def p_valuations(I, p, factor_basis):
    ideal_data = factor_basis[p]
    valuations = [0 for _ in range(len(ideal_data))]
    for i in range(len(ideal_data)):
        while ideal_data[i].divides(I):
            valuations[i] += 1
            I = I / ideal_data[i]
    return (valuations, I)
        
def find_valuation_vector(element, factor_basis):
    K = element.parent()
    result = {}
    current = K.ideal([element])
    for p in factor_basis:
        result[p], current = p_valuations(current, p, factor_basis)
    assert current == K.ideal([1])
    return result

def find_sieving_distances(norm_poly, p, a):
    """Computes the sieving start and distances, i.e. the cosets [b] for which N(a X + b)
    is divisible by p. 
    
    The return value is (start, distances) where distances contains positive integers such that all cosets are 
    start, start + distances[0], start + distances[0] + distances[1], ..., start + distances[0] + ... + distances[-1] = start + p;
    The advantage of this format is that one can start with some begin value congruent to start and step by consecutive
    entries of distances to easily iterate through all such b within an interval."""
    poly_ring = PolynomialRing(ZZ, ['X'])
    f = poly_ring(norm_poly(A = a, B = X)).change_ring(GF(p))
    points = [ZZ(r) for (r, _) in f.roots()]
    if len(points) == 0:
        return None
    points = sorted(points)
    distances = [*[points[i] - points[i - 1] for i in range(1, len(points))], p + points[0] - points[-1]]
    assert sum(distances) == p
    return (points[0], distances)

def sieve_prime(start, end, p, sieving_start, sieving_distances, sieving_interval):
    """Sieves the given interval by a specified prime, i.e. divides every entry by p
    as often as possible."""
    current = start + p - (start % p) + sieving_start
    while True:
        for d in sieving_distances:
            # this can only happen if the number field is Z
            if sieving_interval[current - start] != 0:
                while sieving_interval[current - start] % p == 0:
                    sieving_interval[current - start] = sieving_interval[current - start] / p
            current += d
            if current >= end:
                return

def sieve(start, end, factor_basis, norm_poly, a):
    """Sieves the interval [N(a X + start); N(a X + end)[, i.e. considers the elements a X + i
    where i in [start; end[ and divides every element as often as possible by primes in the factor
    base. In other words, after sieving each entry is coprime to the factor base, and +/- 1 if and
    only if N(a X + i) is factor_basis-smooth"""
    sieving_data = {}
    for p in factor_basis:
        sieving_data[p] = find_sieving_distances(norm_poly, p, a)

    sieving_interval = [norm_poly(a, b) for b in range(start, end)]

    for p in factor_basis:
        if sieving_data[p] is None:
            continue
        sieving_start, sieving_distances = sieving_data[p]
        sieve_prime(start, end, p, sieving_start, sieving_distances, sieving_interval)
    return sieving_interval

def sieve_relations(diamond: Diamond, factor_basis):
    A, B = PolynomialRing(ZZ, ['A', 'B']).gens()
    norm_polys = (
        A.parent()(diamond.left.gen().minpoly()(-B/A) * (-A)**diamond.left.degree()),
        A.parent()(diamond.right.gen().minpoly()(-B/A) * (-A)**diamond.right.degree())
    )
    start = -500
    end = 500
    for a in range(-2, 2):
        if a == 0:
            continue

        sieving_interval = (
            sieve(start, end, factor_basis[0], norm_polys[0], a),
            sieve(start, end, factor_basis[1], norm_polys[1], a)
        )

        for i in range(len(sieving_interval[0])):
            if (sieving_interval[0][i] == 1 or sieving_interval[0][i] == -1) and (sieving_interval[1][i] == 1 or sieving_interval[1][i] == -1):
                b = i + start
                left = a * diamond.left.gen() + b
                right = a * diamond.right.gen() + b
                yield (SmoothElement(left, find_valuation_vector(left, factor_basis[0])), SmoothElement(right, find_valuation_vector(right, factor_basis[1])))

def enter_relation_in_matrix(relation, matrix, row, prime_index_map):
    for p in relation.p_valuations:
        v = relation.p_valuations[p]
        for j in range(len(v)):
            matrix[row, prime_index_map[p] + j] = v[j]

def find_congruent_square(diamond: Diamond, relations, factor_basis):
    m = len(relations[0])
    counter = 0
    prime_index_map = ({}, {})
    for p in factor_basis[0]:
        prime_index_map[0][p] = counter
        counter += len(factor_basis[0][p])
    for p in factor_basis[1]:
        prime_index_map[1][p] = counter
        counter += len(factor_basis[1][p])

    n = counter
    A = Matrix(GF(2), m, n)

    for i in range(m):
        enter_relation_in_matrix(relations[0][i], A, i, prime_index_map[0])
        enter_relation_in_matrix(relations[1][i], A, i, prime_index_map[1])

    for g in kernel(A).gens():

        left = product(relations[0][i].element ** ZZ(g[i]) for i in range(m))
        right = product(relations[1][i].element ** ZZ(g[i]) for i in range(m))

        if left.is_square() and right.is_square():
            left = diamond.lp(sqrt(left))
            right = diamond.rp(sqrt(right))

            print("found congruent square: " + str(left) + "; " + str(right))
            if left != right and left != -right:
                return (gcd(diamond.N, ZZ(left - right)), gcd(diamond.N, ZZ(left + right)))

N = 103 * 127
P = PolynomialRing(ZZ, ['X'])
X = P.gen(0)
diamond = Diamond(X - 162, X**2 - 82, 162, N)
B = 40

factor_basis = (gen_factor_basis(B, diamond.left), gen_factor_basis(B, diamond.right))
factor_basis_len = sum(len(v) for v in factor_basis[0].values()) + sum(len(v) for v in factor_basis[1].values())
relations = ([], [])

# add the trivial relations
for p in Primes():
    if p > B:
        break
    relations[0].append(SmoothElement(diamond.left(p), find_valuation_vector(diamond.left(p), factor_basis[0])))
    relations[1].append(SmoothElement(diamond.right(p), find_valuation_vector(diamond.right(p), factor_basis[1])))

# sieve for more relations
for relation in sieve_relations(diamond, factor_basis):
    relations[0].append(relation[0])
    relations[1].append(relation[1])
    print("found relation: " + str(relation[0]) + " ~ " + str(relation[1]))
    if len(relations[0]) > factor_basis_len + 50:
        break

p, q = find_congruent_square(diamond, relations, factor_basis)
print("Found " + str(N) + " = " + str(p) + " * " + str(q))