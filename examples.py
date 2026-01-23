from mlabe import *
from random import randbytes

N = 3

def poly_bytes(ct):
    return (ct * D * K) / 8

for num_attrs in [0, 1, 2, 3]:
    print('Number of attributes:', num_attrs)

    (mpk, msk) = setup(N, num_attrs)
    sk = key_gen(mpk, msk, [b'x'] * num_attrs)
    plaintext = randbytes(32)
    ciphertext = encrypt(mpk, [b'x'] * num_attrs, plaintext)
    assert plaintext == decrypt(sk, ciphertext)

    # Master public key size. A, u can be expanded from a seed, as can part of A0.
    (_A, A0, _u) = mpk
    poly_ct = A0.nrows() * (A0.ncols() - 2 * N)
    seed_bytes = 32 * 2  # one for A, u and another for part of A0
    print('Public key size:', poly_bytes(poly_ct) + seed_bytes)

    # Secret key size. S_dec can be recomputed from the decryption attributes.
    (_S_dec, x) = sk
    poly_ct = x.nrows() * x.ncols()
    print('Secret key size:', poly_bytes(poly_ct))

    # Ciphertext size.
    poly_ct = 0
    for part in ciphertext:
        poly_ct += part.nrows() * part.ncols()
    print('Ciphertext size:', poly_bytes(poly_ct))
