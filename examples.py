from mlabe import *
from random import randbytes

import matplotlib.pyplot as plt

def sizes():
    N = 2

    def poly_bytes(ct):
        return (ct * D * K) / 8

    for num_attrs in [0, 1, 2, 3]:
        print('Number of attributes:', num_attrs)

        (mpk, msk) = setup(N, num_attrs)
        sk = key_gen(mpk, msk, [b'x'] * num_attrs)
        plaintext = randbytes(D // 8)
        ciphertext = encrypt(mpk, [b'x'] * num_attrs, plaintext)
        assert plaintext == decrypt(sk, ciphertext)

        # Master public key size. X, u can be expanded from a seed.
        (_X, A, _u) = mpk
        poly_ct = A.nrows() * A.ncols()
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

def plot_ciphertext_dist():
    N = 3
    num_attrs = 2
    (mpk, msk) = setup(N, num_attrs)
    sk = key_gen(mpk, msk, [b'x'] * num_attrs)
    ciphertext = encrypt(mpk, [b'x'] * num_attrs, [1] * (D // 8))
    bucket_counts = [0] * Q
    for part in ciphertext:
        for i in range(part.nrows()):
            for j in range(part.ncols()):
                coef = part[i,j].list()
                for d in range(D):
                    bucket_counts[coef[d]] += 1

    # Create labels for the x-axis (e.g., Bucket 0, Bucket 1, etc.)
    # We use range(len(data)) to position the bars correctly
    labels = [f"Bucket {i}" for i in range(len(bucket_counts))]
    x_positions = range(len(bucket_counts))

    # Create the plot
    plt.figure(figsize=(10, 6))
    plt.bar(x_positions, bucket_counts, color='skyblue', edgecolor='black', width=0.8)

    # Adding aesthetics
    plt.title('Coefficient frequencies', fontsize=14)
    plt.xlabel('Coefficient', fontsize=12)
    plt.ylabel('Count', fontsize=12)
    #plt.xticks(x_positions, labels) # Set the x-ticks to match our bucket labels
    plt.grid(axis='y', linestyle='--', alpha=0.7)

    # Show the plot
    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    sizes()
    #plot_ciphertext_dist()
