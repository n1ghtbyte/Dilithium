# -*- mode: sage-shell:sage -*-
from Crypto.Hash import SHAKE128, SHAKE256
from sage.cpython.string import str_to_bytes, bytes_to_str



k = 2  # number of rows
l = 2  # number of columns
eta = 2 # range of small polynomials
#n = 4  # Degree of X^n + 1
n = 256
lamb  = 128 # collision strenght of c tilda
tau = 39
q = 2^23 - 2^13 + 1  # Finite field Z_q
#q = 7  # Finite field Z_q
gamma_1 = 2^17
gamma_2 = (q-1)/88
beta = tau * eta

q = 16417
gamma_2 = (q-1)/32
n = 4
k = 3
l = 2
eta = 10
gamma_1 = 1024
tau =  4
beta = 40

Rmod = PolynomialRing(GF(q), 'x')
x = Rmod.gen()
Rq = Rmod.quotient(x^n + 1, 'a')
a = Rq.gen()

# for functions that not need the reduction mod q
R = PolynomialRing(ZZ, 'o')
o = R.gen()
RR = R.quotient(x^n + 1, 'b')
b = RR.gen()

M = MatrixSpace(Rq, k, l)


def mod_centered(m, alpha):
  """
  Compute m' such that -ceil(alpha / 2) < m' <= floor(alpha / 2) and m ≡ m' (mod alpha).
 
  Parameters:
  m (int): The input integer.
  alpha (int): The modulus.
 
  Returns:
  int: The centered modulo result m'.
  """
  m_mod_alpha = Integer(m) % alpha  # Compute m modulo alphao
  if m_mod_alpha > alpha // 2: # python division floors the result
      m_mod_alpha -= alpha
  assert math.ceil(alpha/2)*(-1) < m_mod_alpha <= math.floor(alpha/2)
  return m_mod_alpha


def bytes_to_bits(b):
    return [((byte >> i) & 1) for byte in b for i in range(8)]


def bits_to_integer(bits, n_bits):
    bits = bits[:n_bits] + [0] * max(0, n_bits - len(bits))
    return sum((bit << i) for i, bit in enumerate(bits))


def bit_unpack(v_bytes, a, b):
    """
    Implements Algorithm 19: BitUnpack(v, a, b)
    v: byte string of length 32 * bitlen(a + b)
    a, b: integers (e.g., from parameter sets)
    Returns: List of 256 integers in the interval [b - 2^c + 1, b], where c = bitlen(a + b)
    """
    c = (a + b).bit_length()
    z = bytes_to_bits(v_bytes)
    w = []

    for i in range(256):
        bits_i = z[i * c : (i + 1) * c]
        val = bits_to_integer(bits_i, c)
        coeff = b - val
        w.append(coeff)

    return w


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
        val = int.from_bytes(b, 'little') % q
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
            rho_prime = rho +  s.to_bytes(1, 'little')+ r.to_bytes(1, 'little')
            A[r][s] = gen_polynomials(rho_prime)
    return  M(A)


"""
Generate keys, given a seed xi, returns pk and sk
"""
def key_gen(xi: bytes):                                                           
    expansion = H256(xi, 1024//8)                                                          
    rho, rho_prime, K = expansion[:256//8], expansion[256//8:256//8 + 512//8], expansion[256//8 + 512//8:]
    A = ExpandA(rho)
    s_1, s_2 = ExpandS(rho_prime)
    t = A*s_1 + s_2
    tr = H256(rho + str_to_bytes(str(t)), 512//8)
    pk = (rho, t)
    sk = (rho, K, tr, s_1, s_2)
    return pk, sk


########
# Sign #
########


def ExpandMask(rho: bytes, mu: int):
    poly_list = []
    n_bits = (2 * eta).bit_length()

    for r in range(l):
        domain_input = (mu + r).to_bytes(2, 'little')
        shake = SHAKE256.new()
        shake.update(rho_prime + domain_input)
        n_bytes = (n * n_bits + 7) // 8
        buf = shake.read(n_bytes)
        coeffs = bit_unpack(buf, n, n_bits)
        poly = Rq(coeffs)
        poly_list.append(poly)

    return vector(poly_list)


def decompose(r):
    r_plus = Integer(r) % q
    r_0 = mod_centered(r_plus, 2*gamma_2)
    if (r_plus - r_0 == q - 1):
        r_1 = 0
        r_0 -= 1
    else:
        r_1 = (r_plus - r_0) // (2 * gamma_2)
    return (r_1, r_0)


def HighBits(r):
    return decompose(r)[0]

def LowBits(r):
    return decompose(r)[1]


def SampleInBall(rho: bytes):
    c = [0] * n
    shake = SHAKE256.new()                                                              
    shake.update(rho)                                                                  
    h = bytes_to_bits(shake.read(8))

    used = set()
    for i in range(n - tau, n):
        while True:
            j = int.from_bytes(shake.read(1), "little")
            if j <= i and j not in used:
                used.add(j)
                break

        c[i] = c[j]
        c[j] = 1 if h[i + tau - n] == 0 else -1

    # fips says this returns in R, but in the notation they say
    # that c is in Rq, what is going on
    return Rq(c)


def inf_norm_scalar(w):
    """Infinity norm for an integer or Zmod(q) element."""
    return abs(mod_centered(w, q))


def inf_norm_poly(p):
    """Infinity norm for a polynomial f in Z[x] or Z_q[x]."""
    coeffs = p.list()
    return max(inf_norm_scalar(c) for c in coeffs)


def inf_norm_vector(poly_vec):
    """Infinity norm for a vector of polynomials over Z or Z_q."""
    return max(inf_norm_poly(f) for f in poly_vec)

#    pk = (rho, t)
#    sk = (rho, K, tr, s_1, s_2)
def sign_message(pk, sk, m: bytes):
    A = ExpandA(pk[0])
    mu = H256(sk[2] + m, 512//8)
    rho_double_prime = H256(sk[1] + mu, 512//8)

    # rejection sampling loop

    kappa = 0
    found = False
    while found != True:
        y = ExpandMask(rho_double_prime, kappa)
        w = A * y
        w_1 = [f.parent()([HighBits(c) for c in f.list()]) for f in w]
        print(f'w1: {w_1_prime}')
        c_tilda = H256(mu + str_to_bytes(str(w_1)), 2*lamb//8) # same as in the fips, they divide by 4
        c = SampleInBall(c_tilda)
        z = y + c*sk[3]
        r_0 = [f.parent()([LowBits(c) for c in f.list()]) for f in (w-c*sk[4])]

        if inf_norm_vector(z) < gamma_1 - beta and inf_norm_vector(r_0) < gamma_2 - beta:
            found = True

        kappa += 8
    print(f'Repetitions: {kappa//8}')
    return c_tilda, z



#    pk = (rho, t)
#    sk = (rho, K, tr, s_1, s_2)
def verify_sig(pk, m: bytes, c_tilda, z):
        A = ExpandA(pk[0])
        mu = H256(sk[2] + m, 512//8)
        c = SampleInBall(c_tilda)
        w_1_prime = [f.parent()([HighBits(c) for c in f.list()]) for f in A*z - c*pk[1]]
        print(f'w1_prime: {w_1_prime}')
        return c_tilda == H256(mu + str_to_bytes(str(w_1_prime)), 2*lamb//8)


seed = b'fips could explain things better...'
pk, sk = key_gen(seed)
message = b'Ultra secret message ahahah'
signature = sign_message(pk, sk, message)
print('Checking if they match')
print(verify_sig(pk, message, signature[0], signature[1]))
