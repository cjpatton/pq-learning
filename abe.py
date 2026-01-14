# Proof-of-concept implementation of the inner-product ABE scheme from
# https://eprint.iacr.org/2015/939, Section 6.2.1. The construction is not
# properly parameterized and therefore not suitable as a reference
# implementation.
#
# The scheme is tailored to a particular class of policies:
#
# * The application specifies the number of attributes and their types, e.g.,
#   ["region", "environment"].
#
# * Each decryption key is associated to a value for each attribute, e.g.,
#   ["EU", "prod"].
#
# * Each ciphertext is associated with a setting for a subset of these
#   attributes. For example, if the decryption key is for ["EU", "prod"], then
#   all of the following are valid policies for encryption:
#
#   * ["EU", "prod"]: The decrypter must be in region "EU" and environment
#     "prod".
#
#   * ["EU", None]: The decrypter must be in region "EU", but can be in any
#     environment.
#
#   * [None, "prod"]: The decrypter may be in any region, but must be in
#     environment "prod".
#
#   * [None, None]: The decrypter may be in any region or environment.
#
#   If an attribute of the ciphertext doesn't match the corresponding attribute
#   of the decryption key, then decryption is not possible. (It will return
#   random garbage.)
#
# NOTE The scheme is currently only suitable for encrypting a single bit. To
# make it useful, we need to be able to encrypt (random) 32 bytes so that we
# can use it for key encapsulation. To do so, and to make the scheme faster and
# more compact, we'd need to move to module lattices as in ML-KEM.
#
# NOTE The scheme is only selectively secure, which is weaker than what we
# would hope to achieve for an encryption scheme. We need to figure out if
# achieving full security (https://eprint.iacr.org/2019/365) is realistic.

from random import Random, randbytes
from sage.all import GF, ceil, log, matrix

def uniform_mat_from_rand(rand, n, m, q):
    '''
    Returns a random n by m matrix over GF(q) using the provided source of
    randomness.
    '''
    F = GF(q)

    rows = []
    for i in range(n):
        row = []
        for j in range(m):
            row.append(F(rand.randint(0, q)))
        rows.append(row)
    return matrix(rows)

def rand_uniform_mat(n, m, q):
    '''
    Returns a random n by m matrix over GF(q).
    '''
    return uniform_mat_from_rand(Random(randbytes(32)), n, m, q)

def short_mat_from_rand(rand, n, m, q, b):
    '''
    Returns a random n by m matrix over GF(q) with entries in the range [-b, b)
    using the provided source of randomness.
    '''
    F = GF(q)

    rows = []
    for i in range(n):
        row = []
        for j in range(m):
            row.append(F(rand.randint(-b, b)))
        rows.append(row)
    return matrix(rows)

def rand_short_mat(n, m, q, b):
    '''
    Returns a random n by m matrix over GF(q) with entries in the range [-b, b).
    '''
    return short_mat_from_rand(Random(randbytes(32)), n, m, q, b)

def zero_mat(n, m, q):
    '''
    Returns the n by m matrix over GF(q) with all zero entries.
    '''
    F = GF(q)
    return matrix([[F(0)] * m] * n)

def identity_mat(n, q):
    '''
    Returns the n by n identity matrix over GF(q).
    '''
    F = GF(q)
    return F(1) * matrix.identity(n)

def gadget_mat(n, q):
    '''
    Returns the n by n gadget matrix over GF(q), as specified in 2015/939,
    Section 5.4.3.
    '''
    F = GF(q)
    l = ceil(log(q) / log(2))
    g = [F(2**k) for k in range(l)]

    rows = []
    for i in range(n):
        row = []
        for j in range(n):
            if i == j:
                row += g
            else:
                row += [F(0)] * l
        rows.append(row)
    return matrix(rows)

def gadget_inv(U):
    '''
    Applies the gadget inversion operation to each row of U.
    '''
    q = len(U.base_ring())  # assumes the base ring is GF(q)
    F = GF(q)
    l = ceil(log(q) / log(2))
    n = U.nrows()
    m = U.ncols()

    rows = []
    for j in range(m):
        row = []
        for i in range(n):
            row += [F((int(U[i,j]) >> k) & 1) for k in range(l)]
        rows.append(row)
    return matrix(rows).T

def trapdoor(T):
    '''
    Generates an (almost) uniform matrix M with a secret trapdoor R, as
    specified in 2015/939, Section 5.4.3. The tag matrix T must be invertible.
    '''
    assert T.nrows() == T.ncols()
    q = len(T.base_ring())  # assumes the base ring is GF(q)
    n = T.nrows()
    F = GF(q)
    l = ceil(log(q) / log(2))

    A0 = identity_mat(n, q).augment(rand_uniform_mat(n, n, q))
    R0 = rand_short_mat(2*n, n*l, q, 13)

    M = A0.augment(T * gadget_mat(n, q) - A0 * R0)
    R = R0.stack(identity_mat(n*l, q))
    return (M, R)

def sample_trapdoor(T, M, R, u):
    '''
    "Securely" sample an SIS solution M*x = u using the trapdoor R for tag T.

    NOTE This is not actually secure because the distribution of p is
    incorrect.
    '''
    q = len(M.base_ring())  # assumes the base ring is GF(q)
    n = M.nrows()
    m = M.ncols()

    p = rand_short_mat(m, 1, q, 13)
    x = p + R * gadget_inv(T.inverse() * (u - M*p))
    return x

def tag(n, q, i, attribute):
    '''
    Derive an invertible tag matrix from the given index (i) and attribute.
    '''
    assert 0 <= i < 256  # i is encoded with a byte
    F = GF(q)

    if attribute == None:
        return zero_mat(n, n, q)

    # For security purposes, we would want to apply a collision resistant hash
    # function here.
    rand = Random(bytes(i) + attribute)
    H = uniform_mat_from_rand(rand, n, n, q)
    while not H.is_invertible():
        H = uniform_mat_from_rand(rand, n, n, q)
    return H

def enc_attr_to_tags(n, q, attrs):
    assert 0 <= len(attrs) < 255  # 255 is reserved for trapdoor tag
    F = GF(q)

    H = []
    count = 0
    for atter in attrs:
        if atter is not None:
            count += 1
    for i, attr in enumerate(attrs):
        H.append(tag(n, q, i, attr))
    H.append(-F(count) * identity_mat(n, q))
    return H

def dec_attr_to_tags(n, q, attrs):
    assert 0 <= len(attrs) < 255  # 255 is reserved for trapdoor tag

    P = []
    for i, attr in enumerate(attrs):
        assert attr is not None
        P.append(tag(n, q, i, attr).inverse())
    P.append(identity_mat(n, q))
    return P

def setup(n, q, num_attrs):
    G = gadget_mat(n, q)
    T = tag(n, q, 255, b'trapdoor tag')

    (M, R) = trapdoor(T)
    u = rand_uniform_mat(n, 1, q)
    A = rand_uniform_mat(n, G.ncols() * (num_attrs+1), q)
    return ((A, M, u), R)

def key_gen(mpk, msk, attrs):
    (A, M, u) = mpk
    R = msk

    n = M.nrows()
    q = len(M.base_ring())  # assumes the base ring is GF(q)
    l = ceil(log(q) / log(2))
    G = gadget_mat(n, q)
    T = tag(n, q, 255, b'trapdoor tag')
    P = dec_attr_to_tags(n, q, attrs)
    assert len(P) == len(attrs) + 1
    assert M.ncols() == n*(2+l)
    assert R.nrows() == n*(2+l)
    assert R.ncols() == n*l
    assert A.nrows() == n
    assert A.ncols() == G.ncols() * len(P)

    S_dec = gadget_inv(P[0]*G)
    for i in range(1, len(P)):
        S_dec = S_dec.stack(gadget_inv(P[i]*G))
    B_dec = A * S_dec

    y = rand_short_mat(B_dec.ncols(), 1, q, 13)
    x = sample_trapdoor(T, M, R, u - B_dec*y).stack(y)
    assert M.augment(B_dec) * x == u
    return (S_dec, x)

def encrypt(mpk, attrs, plaintext):
    assert 0 <= plaintext < 2
    (A, M, u) = mpk

    n = M.nrows()
    q = len(M.base_ring())  # assumes the base ring is GF(q)
    F = GF(q)
    G = gadget_mat(n, q)
    H = enc_attr_to_tags(n, q, attrs)

    S_enc = H[0]*G
    for i in range(1, len(H)):
        S_enc = S_enc.augment(H[i]*G)
    B_enc = A + S_enc

    s = rand_short_mat(1, n, q, 13)
    ciphertext = (
        s * M,
        s * B_enc,
        s * u + F(plaintext * (q // 2)),
    )
    return ciphertext

def decrypt(sk, ciphertext):
    (S_dec, x) = sk
    (c0, c1, c2) = ciphertext
    q = len(c0.base_ring())  # assumes the base ring is GF(q)

    p = c0.augment(c1 * S_dec) * x - c2
    return int(p[0,0]) // (q // 2)
