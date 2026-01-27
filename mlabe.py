# Implementation of the ABE scheme from https://eprint.iacr.org/2015/939,
# Section 6.2.1 using module LWE instead of plain LWE.

from random import Random, randbytes, randint
from sage.all import GF, PolynomialRing, ceil, log, matrix

Q = 3329
D = 256
K = ceil(log(Q) / log(2))
F = GF(Q)
R = PolynomialRing(F, 'x').quotient(f'x^{D} + 1')
B = 57

def zero_mat(N, M):
    '''
    Returns the N by N all-zero matrix over R.
    '''
    out = [[R(0)] * M for _ in range(N)]
    return matrix(out)

def identity_mat(N):
    '''
    Returns the N by N identity matrix over R.
    '''
    out = zero_mat(N, N)
    for i in range(N):
        out[i,i] = R(1)
    return matrix(out)

def uniform_mat_from_rand(rand, N, M):
    '''
    Returns a random N by M matrix over R using the provided source of
    randomness.
    '''
    rows = []
    for n in range(N):
        row = []
        for m in range(M):
            poly = []
            for d in range(D):
                poly.append(F(rand.randint(0, Q)))
            row.append(R(poly))
        rows.append(row)
    return matrix(rows)

def rand_uniform_mat(N, M):
    '''
    Returns a random N by M matrix over R.
    '''
    return uniform_mat_from_rand(Random(randbytes(32)), N, M)

def rand_short_mat(N, M):
    '''
    Returns a random N by M matrix over R with coefficients in range [-B, B).
    '''
    rows = []
    for i in range(N):
        row = []
        for j in range(M):
            poly = []
            for d in range(D):
                poly.append(F(randint(-B, B)))
            row.append(R(poly))
        rows.append(row)
    return matrix(rows)

def gadget_inv(U):
    '''
    Find a pre-image X such that G*X = U, where G is the gadget matrix.
    '''
    out = matrix([[R(0)] * U.ncols() for _ in range(U.nrows() * K)])

    for i in range(U.nrows()):
        for j in range(U.ncols()):
            u_coef = U[i,j].list()
            u_bits = [[] for k in range(K)]
            for k in range(K):
                for d in range(D):
                    u_bits[k].append(F((int(u_coef[d]) >> k) & 1))

            for k in range(K):
                out[i*K + k, j] =  R(u_bits[k])

    return out

def gadget(X):
    '''
    Return G*X where G is the gadget matrix.
    '''
    assert X.nrows() % K == 0
    out = matrix([[R(0)] * X.ncols() for _ in range(X.nrows() // K)])

    for i in range(X.nrows() // K):
        for j in range(X.ncols()):
            u_coef = []
            x_coef = [ X[i*K + k, j].list() for k in range(K) ]
            for d in range(D):
                u_coef.append(0)
                for k in range(K):
                    u_coef[d] |= int(x_coef[k][d]) << k
            out[i, j] = R(u_coef)

    return out

def trapdoor(T):
    '''
    Return a(n almost) random matrix A with G-trapdoor R for tag T.
    '''
    assert T.nrows() == T.ncols()
    N = T.nrows()
    G = gadget(identity_mat(N*K))
    W = 2  # TODO Figure out how to set this

    A0 = rand_uniform_mat(N, W*N)
    R0 = rand_short_mat(W*N, K*N)
    A = A0.augment(T*G - A0*R0)
    R = R0.stack(identity_mat(N*K))
    return (A, R)

def sample_trapdoor(T, A, R, u):
    '''
    Sample a solution x to A*x = u using the G-trapdoor R for tag T.
    '''
    N = A.nrows()
    M = A.ncols()

    # TODO Figure out how securely sample p.
    p = rand_short_mat(M, 1)
    x = p + R * gadget_inv(T.inverse() * (u - A*p))
    return x

def tag(N, i, attr):
    '''
    Derive an invertible tag matrix from the given index (i) and attribute.
    '''
    assert 0 <= i < 256  # i is encoded with a byte
    if attr == None:
        return zero_mat(N, N)

    # TODO Use a XOF here to ensure tag matrix derivation is collision
    # resistant (e.g., SHAKE128).
    rand = Random(bytes(i) + attr)
    H = uniform_mat_from_rand(rand, N, N)
    while not H.is_invertible():
        H = uniform_mat_from_rand(rand, N, N)
    return H

def enc_attr_to_tags(N, attrs):
    '''
    Derive the tag matrices for a sequence of encryption attributes. If the
    inner product of these matrices with the decryption tags is zero, then
    decryption will succeed. Otherwise, decryption will fail.
    '''
    H = []
    count = 0
    for atter in attrs:
        if atter is not None:
            count += 1
    for (i, attr) in enumerate(attrs):
        H.append(tag(N, i, attr))
    H.append(R(-count) * identity_mat(N))
    return H

def dec_attr_to_tags(N, attrs):
    '''
    Derive the tag matrices for a sequence of decryption attributes. If the
    inner product of these matrices with the encryption tags is zero, then
    decryption will succeed. Otherwise, decryption will fail.
    '''
    P = []
    for (i, attr) in enumerate(attrs):
        assert attr is not None
        P.append(tag(N, i, attr).inverse())
    P.append(identity_mat(N))
    return P

def setup(N, num_attrs):
    '''
    Generate the master public key and master secret key for the given number
    of attributes.
    '''
    G = gadget(identity_mat(N*K))
    T = identity_mat(N)
    (A, R) = trapdoor(T)
    u = rand_uniform_mat(N, 1)
    X = rand_uniform_mat(N, G.ncols() * (num_attrs+1))
    return ((X, A, u), R)

def key_gen(mpk, msk, attrs):
    '''
    Generate a decryption key for the given attributes.
    '''
    (X, A, u) = mpk
    R = msk
    N = A.nrows()
    G = gadget(identity_mat(N*K))
    T = identity_mat(N)
    P = dec_attr_to_tags(N, attrs)

    S_dec = gadget_inv(P[0]*G)
    for i in range(1, len(P)):
        S_dec = S_dec.stack(gadget_inv(P[i]*G))
    B_dec = X * S_dec

    y = rand_short_mat(B_dec.ncols(), 1)
    x = sample_trapdoor(T, A, R, u - B_dec*y).stack(y)
    assert A.augment(B_dec) * x == u
    return (S_dec, x)

def encrypt(mpk, attrs, plaintext):
    '''
    Encrypt the given plaintext towards the given attributes.
    '''
    assert len(plaintext) == 32
    assert D == 256
    (X, A, u) = mpk
    N = A.nrows()
    G = gadget(identity_mat(N*K))
    H = enc_attr_to_tags(N, attrs)

    p_coef = []
    for l in range(D):
        p_coef.append((plaintext[l // 8] >> (l % 8)) & 1)
    p = (Q // 2) * R(p_coef)

    S_enc = H[0]*G
    for i in range(1, len(H)):
        S_enc = S_enc.augment(H[i]*G)
    B_enc = X + S_enc

    s = rand_short_mat(1, N)
    ciphertext = (
        s * A,
        s * B_enc,
        s * u + p,
    )
    return ciphertext

def decrypt(sk, ciphertext):
    '''
    Decrypt the given ciphertext. If the encryption attributes don't match the
    attributes associated with the decryption key, then the result will be
    incorrect.
    '''
    assert D == 256
    (S_dec, x) = sk
    (c0, c1, c2) = ciphertext

    p = c0.augment(c1 * S_dec) * x - c2
    p_coef = p[0,0].list()
    p_bytes = [0] * 32
    for l in range(D):
        bit = int(p_coef[l]) // (Q // 2)
        p_bytes[l // 8] |= bit << (l % 8)
    return bytes(p_bytes)
