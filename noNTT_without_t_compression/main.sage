# -*- mode: sage-shell:sage -*-
from Crypto.Hash import SHAKE128, SHAKE256



k = 2  # number of rows
l = 2  # number of columns
eta = 2 # range of small polynomials
n = 4  # Degree of X^n + 1
q = 2^23 - 2^13 + 1  # Finite field Z_q
q = 7  # Finite field Z_q

lambda  = 128 # collision strenght of c tilda

R = PolynomialRing(GF(q), 'x')
x = R.gen()
Rq = R.quotient(x^n + 1, 'a')
a = Rq.gen()
M = MatrixSpace(Rq, k, l)

def H256(seed: bytes, length: int) -> bytes:                                               
    shake = SHAKE256.new()                                                              
    shake.update(seed)                                                                  
    return shake.read(length)


def H128(seed: bytes, length: int) -> bytes:                                               
    shake = SHAKE128.new()                                                              
    shake.update(seed)                                                                  
    return shake.read(length)


def coeffFromHalfByte(z):
    val = z & 0xF  # lower 4 bits
    if val <= 2 * eta:
        return val - eta
    return None


def rejBoundedPoly(seed: bytes):
    shake = SHAKE256.new()
    shake.update(seed)
    stream = shake.read(512)  # get enough bytes
    j = 0
    a = []

    i = 0
    while j < n:
        if i >= len(stream):
            # extend stream if needed
            stream += shake.read(256)
        z = stream[i]
        z0 = coeffFromHalfByte(z & 0xF)
        z1 = coeffFromHalfByte(z >> 4)

        if z0 is not None:
            a.append(GF(q)(z0))
            j += 1
        if z1 is not None and j < n:
            a.append(GF(q)(z1))
            j += 1
        i += 1

    poly = Rq(sum(a[i] * x^i for i in range(n)))
    return poly


def ExpandS(rho):
    s1 = [None] * l
    s2 = [None] * k

    for r in range(l):
        seed = rho + r.to_bytes(2, "little")
        s1[r] = Rq(rejBoundedPoly(seed))

    for r in range(k):
        seed = rho + (r + l).to_bytes(2, "little")
        s2[r] = Rq(rejBoundedPoly(seed))

    return vector(s1), vector(s2)

def gen_polynomials(rho):
    shake = SHAKE128.new()
    shake.update(rho)
    
    coeffs = []
    while len(coeffs) < n:
        b = shake.read(2) # 2 bytes
        val = int.from_bytes(b, 'big') % q
        coeffs.append(val)

    poly = Rq(sum(coeffs[i] * x^i for i in range(n)))
    
    return poly


"""
This function does not produce elements in T_q but in R_q,
because we are not working with the NTT.
"""
def ExpandA(rho: bytes):
    A = [[None for _ in range(l)] for _ in range(k)]
    for r in range(k):
        for s in range(l):
            rho_prime = rho +  s.to_bytes(1, 'big')+ r.to_bytes(1, 'big')
            A[r][s] = gen_polynomials(rho_prime)
    return  M(A)


def key_gen(xi: bytes):                                                           
    expansion = H256(xi, 1024//8)                                                          
    rho, rho_prime, K = expansion[:256//8], expansion[256//8:256//8 + 524//8], expansion[256//8 + 524//8:]
    A = ExpandA(rho)
    s_1, s_2 = ExpandS(rho_prime)
    t = A*s_1 + s_2
    pk = (rho, t)
    sk = (rho, K, 
    return A, s_1, s_2, t

