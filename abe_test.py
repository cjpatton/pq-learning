from abe import *
from sage.all import GF, ceil, log, matrix
from unittest import TestCase

class TestAbe(TestCase):
    def test_gadget_mat(self):
        n = 5
        q = 101
        G = gadget_mat(n, q)

        u = rand_uniform_mat(n, 1, q)
        x = gadget_inv(u)
        self.assertEqual(G*x, u)

        U = rand_uniform_mat(n, q, 101)
        X = gadget_inv(U)
        self.assertEqual(G*X, U)

    def test_trapdoor(self):
        n = 10
        q = 3329
        l = ceil(log(q) / log(2))
        m = n*(2+l)

        # Pick a tag for the trapdoor.
        T = tag(n, q, 255, b'hella')
        (A, R) = trapdoor(T)
        self.assertEqual(A.nrows(), n)
        self.assertEqual(A.ncols(), m)
        self.assertEqual(R.nrows(), m)
        self.assertEqual(R.ncols(), n*l)
        self.assertEqual(A * R, T * gadget_mat(n, q))

        u = rand_uniform_mat(n, 1, q)
        x = sample_trapdoor(T, A, R, u)
        self.assertEqual(A * x, u)


    def test_tag_is_invertible(self):
        self.assertTrue(tag(100, 3329, 0, b'hella').is_invertible())
        self.assertTrue(tag(100, 3329, 254, b'hella').is_invertible())

    def test_policy(self):
        n = 10
        q = 3329
        F = GF(q)

        test_cases = [
            {
                'enc_attributes': [],
                'dec_attributes': [],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU'],
                'dec_attributes': [b'EU'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [None, None],
                'dec_attributes': [b'EU', b'prod'],
                'expect_valid': True,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'Bikini Bottom', b'prod'],
                'expect_valid': False,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'staging'],
                'expect_valid': False,
            },
        ]

        for t in test_cases:
            self.assertEqual(len(t['enc_attributes']), len(t['dec_attributes']))

            H_enc = enc_attr_to_tags(n, q, t['enc_attributes'])
            H_dec = dec_attr_to_tags(n, q, t['dec_attributes'])
            self.assertEqual(len(H_enc), len(H_dec))
            num_tags = len(H_enc)
            V = zero_mat(n, n, q)
            for i in range(num_tags):
                V += H_enc[i] * H_dec[i]

            self.assertEqual(V.is_zero(), t['expect_valid'], 'test case: {}\n{}'.format(t, V))

    def test_roundtrip(self):
        n = 10
        q = 3329
        num_attrs = 2
        (mpk, msk) = setup(n, q, 2)

        test_cases = [
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'plaintext': 0,
            },
            {
                'enc_attributes': [b'EU', b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'plaintext': 1,
            },
            {
                'enc_attributes': [None, b'prod'],
                'dec_attributes': [b'EU', b'prod'],
                'plaintext': 1,
            },
            {
                'enc_attributes': [b'EU', None],
                'dec_attributes': [b'EU', b'prod'],
                'plaintext': 1,
            },
            {
                'enc_attributes': [None, None],
                'dec_attributes': [b'EU', b'prod'],
                'plaintext': 1,
            },
        ]

        for t in test_cases:
            sk = key_gen(mpk, msk, t['dec_attributes'])
            ciphertext = encrypt(mpk, t['enc_attributes'], t['plaintext'])
            plaintext = decrypt(sk, ciphertext)
            self.assertEqual(plaintext, t['plaintext'])
