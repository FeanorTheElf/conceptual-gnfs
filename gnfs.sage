

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

    def __init__(self, element, p_valuations, character_values):
        self.element = element
        self.p_valuations = p_valuations
        self.character_values = character_values

    def __repr__(self) -> str:
        return str(self.element)

class SplitPrimeIdeal:
    """A prime ideal of the form (p, x + s) where x is an integral primitive element
    of the number field."""

    def __init__(self, norm, s) -> None:
        assert norm.is_prime()
        self.norm = norm
        self.s = s

    def in_quotient_field(self, element):
        return element.polynomial().change_ring(ZZ)(self.s)

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

def gen_character_basis(B, size, K):
    result = []
    f = K.gen().minpoly()
    current = next_prime(B)
    for _ in range(size):
        p = current
        roots = f.change_ring(GF(p)).roots()
        if len(roots) == K.degree():
            result.append(SplitPrimeIdeal(p, roots[0][0]))
        current = next_prime(current + 1)
    return result

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

def find_character_vector(element, character_basis):
    K = element.parent()
    return [
        0 if p.in_quotient_field(element).is_square() else 1 for p in character_basis
    ]

def find_relation_data(element, factor_basis, character_basis) -> SmoothElement:
    return SmoothElement(
        element, 
        find_valuation_vector(element, factor_basis),
        find_character_vector(element, character_basis)
    )

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

def sieve_relations(diamond: Diamond, factor_basis, character_basis):
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
                yield (
                    find_relation_data(left, factor_basis[0], character_basis[0]), 
                    find_relation_data(right, factor_basis[1], character_basis[1])
                )

def enter_relation_in_matrix(relation, matrix, row, prime_index_map, character_index_start):
    for p in relation.p_valuations:
        v = relation.p_valuations[p]
        for j in range(len(v)):
            matrix[row, prime_index_map[p] + j] = v[j]
    for i in range(len(relation.character_values)):
        matrix[row, character_index_start + i] = relation.character_values[i]

def find_congruent_square(diamond: Diamond, relations, factor_basis, character_basis):
    m = len(relations[0])
    counter = 0
    prime_index_map = ({}, {})
    for p in factor_basis[0]:
        prime_index_map[0][p] = counter
        counter += len(factor_basis[0][p])
    for p in factor_basis[1]:
        prime_index_map[1][p] = counter
        counter += len(factor_basis[1][p])

    character_index_start = (counter, counter + len(character_basis[0]))
    n = counter + len(character_basis[0]) + len(character_basis[1])
    A = Matrix(GF(2), m, n)

    for i in range(m):
        enter_relation_in_matrix(relations[0][i], A, i, prime_index_map[0], character_index_start[0])
        enter_relation_in_matrix(relations[1][i], A, i, prime_index_map[1], character_index_start[1])

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
character_basis = ([], gen_character_basis(B, 20, diamond.right))
relations = ([], [])
constraints_len = sum(len(v) for v in factor_basis[0].values()) + sum(len(v) for v in factor_basis[1].values()) + len(character_basis[0]) + len(character_basis[1])

print("Left field is " + str(diamond.left))
print("   Using factor basis with " + str(sum(len(factor_basis[0][p]) for p in factor_basis[0])) + " elements")
print("   Using quadratic character basis with " + str(len(character_basis[0])) + " elements")
print()
print("Right field is " + str(diamond.left))
print("   Using factor basis with " + str(sum(len(factor_basis[1][p]) for p in factor_basis[1])) + " elements")
print("   Using quadratic character basis with " + str(len(character_basis[1])) + " elements")
print()

# add the trivial relations
for p in Primes():
    if p > B:
        break
    relations[0].append(find_relation_data(diamond.left(p), factor_basis[0], character_basis[0]))
    relations[1].append(find_relation_data(diamond.right(p), factor_basis[1], character_basis[1]))

# sieve for more relations
for relation in sieve_relations(diamond, factor_basis, character_basis):
    relations[0].append(relation[0])
    relations[1].append(relation[1])
    print("found relation: " + str(relation[0]) + " ~ " + str(relation[1]))
    if len(relations[0]) > constraints_len + 5:
        break

p, q = find_congruent_square(diamond, relations, factor_basis, character_basis)
print("Found " + str(N) + " = " + str(p) + " * " + str(q))